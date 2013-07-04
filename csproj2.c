#include <stdio.h>
#include <string.h>
#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "tree.h"
#include "cgraph.h"
#include "hashtab.h"
#include "langhooks.h"
#include "tree-iterator.h"

bool VarInUse;					// Whether this variable is used
int FunNum;						// # of functions
int GlobalNum;					// # of global variables
struct VarInfo *GloVar;			
struct FunInfo *func;
struct CallNode *CallRoot;
struct CallNode *CurCall;		// fidrent node for call graph
FILE *fp;
int GlobalUninit = 1;
int GetName(tree node, char *name);
void UseVar(char *name, int fid, bool *init);
void DefVar(char *name, int fid, bool *init);
void FuncIter(tree node, int fid);
void TravArg(tree node, int fid);
void TravVar(tree node, int fid);
int Traverse(tree node, int fid, bool *init);
void OutputLocal(struct CallNode *node);
void OutputGlobal();

struct CallNode{
  struct CallNode *list[10];
  struct CallNode *parent;
  int dfsstatus;
  int funID;
  int child;
};

struct GotoLabel{
  int label;
  bool VarInfo[20];
};

struct GotoLabelList{
  int fidnum;
  struct GotoLabel labels[10];
};

struct TotalLabels{
  int fidnum;
  int LabelList[20];
};

struct FunInfo{
  char name[30];				// name of the function
  int num_arg;					// number of arguments
  struct VarInfo *arg;			// information of arguments
  int num_var;					// number of local variable
  int uninit_num;				// number of uninitialized variable
  struct VarInfo *var;			// information of variables
  tree root;					// root of the function
  struct GotoLabelList label_list;	// future label list
  struct TotalLabels exist_list;	// TotalLabels label list
  bool *init_var;				// if the variables are initialized in this function
  bool fid_var[30];
  bool switch_var[30];
  bool in_switch;
  bool switch_goto;
  int switch_label;
  int graph;
  bool finish;					// if we have already analyzed the function
};

struct VarInfo{
  char name[30];
  bool init;
  int usebfinit;
};

void cs502_proj2()
{
  struct cgraph_node *node;
  struct cgraph_node *node_end;
  struct varpool_node *var;
  tree vardecl, fndecl;
  int i;
  char name[30];
  fp = fopen("output.txt", "w");
  GlobalNum = 0;
  GloVar = NULL;
  for(var = varpool_nodes; var; var = var->next){
    GlobalNum++;
  }	// get the number of global vars
  if(0 < GlobalNum){
    GloVar = (struct VarInfo*) xmalloc (sizeof(struct VarInfo) * GlobalNum);
	i = 0;
	// Initialize every global variable
	for(var = varpool_nodes; var; var = var->next){
	  vardecl = var->decl;
	  if(GetName(vardecl, name)){
		strcpy(GloVar[i].name, name);
		if(DECL_INITIAL(vardecl))	// If a variable is initialized
		  GloVar[i].init = true;
		else if(INTEGER_TYPE != TREE_CODE(TREE_TYPE(vardecl)) && REAL_TYPE != TREE_CODE(TREE_TYPE(vardecl))) 
		  GloVar[i].init = true;	// we focus on scalar variable
		else
		  GloVar[i].init = false;
		GloVar[i].usebfinit = 0;
		i++;
	  }
	}
  }
  // Retrieve number of the functions and their names
  FunNum = 0;
  func = NULL;
  for (node = cgraph_nodes; node; node = node->next) {
		FunNum++;
  }		// Same to global variable, we at first get the number of functions
  
  // Initialize function info and get the main function
  int main_num;
  tree main_node;
  if(0 < FunNum){	// Initialize all of the functions
    func = (struct FunInfo*) xmalloc (sizeof(struct FunInfo) * FunNum);
	i = 0;
	for(node = cgraph_nodes; node; node = node->next){
	  fndecl = node->decl;
	  strcpy(func[i].name, IDENTIFIER_POINTER(DECL_NAME(fndecl)));
	  if(0 == strcmp("main", IDENTIFIER_POINTER(DECL_NAME(fndecl)))){
	    main_num = i;
		main_node = fndecl;
	  }
	  func[i].arg = NULL;
	  func[i].var = NULL;
	  func[i].init_var = NULL;
	  func[i].root = fndecl;
	  func[i].uninit_num = 0;
	  func[i].label_list.fidnum = 0;
	  func[i].exist_list.fidnum = 0;
	  func[i].finish = false;
	  func[i].in_switch = false;
	  func[i].switch_goto = false;
	  func[i].switch_label = -123;
	  i++;
	}
  }
  else
    printf("No function.\n");

  // Initialize the call graph
  CallRoot = (struct CallNode*) xmalloc(sizeof(struct CallNode));
  CallRoot->dfsstatus = 0;
  CallRoot->funID = main_num;
  CallRoot->child = 0;
  CallRoot->parent = NULL;
  CurCall = CallRoot;
  
  // Analyse the main function first.
  FuncIter(main_node, main_num);
  // Output the results
  OutputLocal(CallRoot);
  OutputGlobal();
  fclose(fp);
}

int GetName(tree node, char *name){
  tree temp = node;
again: 
  switch(TREE_CODE(temp)){
    case ARRAY_TYPE:
	case RECORD_TYPE: printf("<other type>\n");
	  break;
	case FUNCTION_DECL:
	  strcpy(name, IDENTIFIER_POINTER(DECL_NAME(temp)));
	  return 2;
  case TYPE_DECL:
  case VAR_DECL:
  case PARM_DECL:
  case FIELD_DECL:
	  strcpy(name, IDENTIFIER_POINTER(DECL_NAME(temp))); 
	  return 1;
	case ADDR_EXPR:
	case INDIRECT_REF:
	case NOP_EXPR:
	  temp = TREE_OPERAND(temp, 0);
	  goto again;
	default: 
	  break;
  }
  return 0;
}

void FuncIter(tree node, int fid){
  int i;
  // for each function, get arguments and varialbes  
  TravArg(node, fid);
  TravVar(node, fid);
  func[fid].init_var = (bool*) xmalloc (sizeof(bool) * (func[fid].num_var + GlobalNum));
  
  // From the previous knowledge, we copy the initialized info for every variable, including the local ones and global ones.
  for(i=0; i<func[fid].num_var; i++)
    func[fid].init_var[i] = func[fid].var[i].init;
  for(i=func[fid].num_var; i<func[fid].num_var+GlobalNum; i++)
    func[fid].init_var[i] =  GloVar[i - func[fid].num_var].init;
  // get the main body of the function
  tree main = DECL_SAVED_TREE(node);
  if(BIND_EXPR != TREE_CODE(main))
    printf("Error in the root of the tree.\n");
  tree bind_body = BIND_EXPR_BODY(main);
  Traverse(bind_body, fid, func[fid].init_var);
  
  // After analysis, we update the initialized information of the global variables
  for(i=func[fid].num_var; i<func[fid].num_var+GlobalNum; i++)
    GloVar[i - func[fid].num_var].init = func[fid].init_var[i];
  return;
}

void TravArg(tree node, int fid){
  tree arg, arg_decl;
  arg = TYPE_ARG_TYPES(TREE_TYPE(node));
  arg_decl = DECL_ARGUMENTS(node);
  // traverse argument nodes
  int num = 0;
  while(arg && arg != void_list_node && arg != error_mark_node){
    num++;
	arg = TREE_CHAIN(arg);
  } 	// get the number
  
  if(0 == num){
    func[fid].num_arg = 0;
	return;
  }
  func[fid].num_arg = num;
  func[fid].arg = (struct VarInfo*) xmalloc(sizeof(struct VarInfo) * num);
  arg = TYPE_ARG_TYPES(TREE_TYPE(node));
  num = 0;
  // Initialize the arguments
  while(arg && arg != void_list_node && arg != error_mark_node){
    GetName(arg_decl, func[fid].arg[num].name);
	func[fid].arg[num].init = true;
	func[fid].arg[num].usebfinit = 0;
	num++;
    arg = TREE_CHAIN(arg);	
	arg_decl = TREE_CHAIN(arg_decl);
  }
  return;
}

void TravVar(tree node, int fid){
  tree main = DECL_SAVED_TREE(node);
  if(BIND_EXPR != TREE_CODE(main)){
    printf("BIND_EXPR != TREE_CODE(main)\n");
	return;
  }
  int num = 0;
  char name[30];
  tree tmp;
  for(tmp = BIND_EXPR_VARS(main); tmp; tmp = DECL_CHAIN(tmp)){
    if(FUNCTION_DECL == TREE_CODE(tmp))
	  continue;
    if(GetName(tmp, name))
      num++;
  }		// get the number of the variable
  if(0 == num){
    func[fid].num_var = 0;
	return;
  }
  func[fid].num_var = num;
  func[fid].var = (struct VarInfo*) xmalloc(sizeof(struct VarInfo) * num);
  num = 0;
  bool temp;
  // Initialize those variable
  for(tmp = BIND_EXPR_VARS(main); tmp; tmp = DECL_CHAIN(tmp)){
    if(FUNCTION_DECL == TREE_CODE(tmp))
	  continue;
    if(GetName(tmp, func[fid].var[num].name)){
	  temp = false;
	  if(DECL_INITIAL(tmp))
	    temp = true;
	  if(INTEGER_TYPE != TREE_CODE(TREE_TYPE(tmp)) && REAL_TYPE != TREE_CODE(TREE_TYPE(tmp))){
	    temp = true;
	  }
	  func[fid].var[num].init = temp;
	  func[fid].var[num].usebfinit = false;
	  num++;
	}
  }
}

void UseVar(char *name, int fid, bool *init){
  int i;
  
  // If the variable is local one
  for(i = 0; i < func[fid].num_var; i++){
    if(0 == strcmp(name, func[fid].var[i].name)){
	  if(init[i] || func[fid].var[i].usebfinit)
	    return;
	  else{
	    if(VarInUse){
		  func[fid].uninit_num++;
	      func[fid].var[i].usebfinit = func[fid].uninit_num;
	      return;
		}
	  }
	}
 }
 
  // Then search the variable in global one
  for(i = 0; i < GlobalNum; i++){
    if(0 == strcmp(name, GloVar[i].name)){
      if(init[i + func[fid].num_var] || GloVar[i].usebfinit > 0 || GloVar[i].init)
	    return;
	  else{
	    GloVar[i].usebfinit = GlobalUninit;
		GlobalUninit++;
	    return;
      }
	}
  }
  
  // If it is not argument, that sounds strange
  for(i = 0; i < func[fid].num_arg; i++){
    if(0 == strcmp(name, func[fid].arg[i].name)){
	  return;
	}
  }
}

void DefVar(char *name, int fid, bool *init){
  int i;
  
  // Local var
  for(i = 0; i < func[fid].num_var; i++){
    if(0 == strcmp(name, func[fid].var[i].name)){
	  init[i] = true;
	  return;
	}
  }
  // Global var
  for(i = 0; i < GlobalNum; i++){
    if(0 == strcmp(name, GloVar[i].name)){
	  if(init[i + func[fid].num_var])
	    return;
	  else{
	    init[i + func[fid].num_var] = true;
	    return;
      }
	}
  }
  // argument could be initialized by pointer
  for(i = 0; i < func[fid].num_arg; i++){
    if(0 == strcmp(name, func[fid].arg[i].name)){
	  func[fid].arg[i].usebfinit = 1;
	  return;
	}
  }
}

int Traverse(tree node, int fid, bool *init){
  tree left, right;
  int i;
  switch(TREE_CODE(node)){
	case BIND_EXPR:
	{
	  tree bind_body = BIND_EXPR_BODY(node);
	  Traverse(bind_body, fid, init);
	  break;
	}
	case STATEMENT_LIST: 
	{
	  tree_stmt_iterator si;
	  for(si = tsi_start(node); !tsi_end_p(si); tsi_next(&si)){
	    tree node_in_list = tsi_stmt(si);
		Traverse(node_in_list, fid, init);
		if(func[fid].in_switch){
		  if(TREE_CODE(node) != CASE_LABEL_EXPR && TREE_CODE(node) != GOTO_EXPR){
		    Traverse(node_in_list, fid, func[fid].switch_var);
		  }
		}
	  }	  
	  break;
	}
	case STRING_CST:
	  break;
	  
	  // this is for array
	case ARRAY_REF:
	{
	  tree op0 = TREE_OPERAND(node, 0);
	  tree op1 = TREE_OPERAND(node, 1);
	  Traverse(op0, fid, init);
	  Traverse(op1, fid, init);
	  break;
	}  
	
	// If the called function is "printf" and "scanf", we know what it do for every arguments.
	case CALL_EXPR:
	{
	  tree fn = CALL_EXPR_FN(node);

	  char call_name[30];
	  GetName(fn, call_name);
	  tree arg;
	  call_expr_arg_iterator iter;
	  if(0 == strcmp("printf", call_name)){
	    VarInUse = true;
	    FOR_EACH_CALL_EXPR_ARG(arg, iter, node){
		  Traverse(arg, fid, init);
		}
		break;
	  }
	  if(0 == strcmp("scanf", call_name)){
	    VarInUse = false;
		
	    FOR_EACH_CALL_EXPR_ARG(arg, iter, node){	
		  Traverse(arg, fid, init);
		}
	    break;
	  }
	  
	  // This part is added at the stuff
	  int i, j, num;
	  for(i=0; i<FunNum; i++){
	    if(0 == strcmp(func[i].name, call_name)){
		  break;
		}
	  }
	  
	  // If it is a new node.
	  if(!func[i].finish){
	    num = CurCall->child;
	    CurCall->list[num] = (struct CallNode*) xmalloc (sizeof(struct CallNode));
	    CurCall->child++;
	    CurCall->list[num]->dfsstatus = 0;
	    CurCall->list[num]->funID = i;
	    CurCall->list[num]->parent = CurCall;
	    CurCall->list[num]->child = 0;
	    CurCall = CurCall->list[num];
	    FuncIter(func[i].root, i);
	    func[i].finish = true;
	    CurCall = CurCall->parent;	  
	  }
	  if(0 < func[i].num_arg){
	    j = 0;
	    FOR_EACH_CALL_EXPR_ARG(arg, iter, node){
		  if(GetName(arg, call_name)){
		    if(func[i].arg[j].usebfinit){
			  DefVar(call_name, fid, init);
			}
		  }
		  j++;
		}
	  }
	  
	  // After every function, update the gloabal info
	  for(i=0; i<GlobalNum; i++){
	   init[func[fid].num_var + i] = GloVar[i].init;
		}
	  break;
	}
	
	case LABEL_EXPR:
	  left = TREE_OPERAND(node, 0);
	  if(!DECL_NAME(left)){
		int label = Traverse(left, fid, init);
		int i, j;
		i = func[fid].exist_list.fidnum;
		func[fid].exist_list.LabelList[i] = label;
		func[fid].exist_list.fidnum++;
		for(i=0; i<func[fid].label_list.fidnum; i++){
		  if(label == func[fid].label_list.labels[i].label){
		    for(j=0; j<func[fid].num_var + GlobalNum; j++){
			  init[j] = func[fid].label_list.labels[i].VarInfo[j];
			}
			break;
		  }
		}
	  }	
	  break;
	  
	case LABEL_DECL:
	  if(LABEL_DECL_UID(node) != -1)
	    return LABEL_DECL_UID(node);
	  else
	    return DECL_UID(node);
	  break;
	case GOTO_EXPR:
	{
	  tree des = GOTO_DESTINATION(node);
	  int label = Traverse(des, fid, init);
	  bool done = false;
	  int i, j;
	  for(i=0; i<func[fid].exist_list.fidnum; i++){
	    if(label == func[fid].exist_list.LabelList[i]){ 
		  done = true;
		  break;
		}
	  }
	  if(done)
	    break;
	  if(func[fid].in_switch){
	    func[fid].switch_goto = true;
		func[fid].switch_label = label;
	  }	
	  for(i=0; i<func[fid].label_list.fidnum; i++){
	    if(label == func[fid].label_list.labels[i].label){
		  if(!func[fid].in_switch){
		    for(j=0; j<func[fid].num_var + GlobalNum; j++)
		      func[fid].label_list.labels[i].VarInfo[j] = func[fid].label_list.labels[i].VarInfo[j] & init[j];
	      }
		  else{
		    for(j=0; j<func[fid].num_var + GlobalNum; j++)
		      func[fid].label_list.labels[i].VarInfo[j] = func[fid].label_list.labels[i].VarInfo[j] & (init[j] & func[fid].switch_var[j]);
		  }
		  done = true;
		  break;
		}
	  }
	  if(done)
	      break;
	  j = func[fid].label_list.fidnum;
	  func[fid].label_list.labels[j].label = label;
	  if(!func[fid].in_switch){
	    for(i=0; i<func[fid].num_var + GlobalNum; i++)
	      func[fid].label_list.labels[j].VarInfo[i] = init[i];
	    func[fid].label_list.fidnum++;
	  }
	  else{
	    for(i=0; i<func[fid].num_var + GlobalNum; i++){
		  func[fid].label_list.labels[j].VarInfo[i] = init[i] & func[fid].switch_var[i];
		func[fid].label_list.fidnum++;
		}
	  }
	  break;
	} 
	
	case SWITCH_EXPR:
	{
	  func[fid].in_switch = true;
	  int i, j;
	  VarInUse = true;
      Traverse(SWITCH_COND(node), fid, init);

	  for(i=0; i<func[fid].num_var + GlobalNum; i++){
	    func[fid].fid_var[i] = init[i];
		func[fid].switch_var[i] = init[i];
	  }
	  func[fid].switch_goto = false;
	  Traverse(SWITCH_BODY(node), fid, init);
	  if(func[fid].switch_label != -123){
	    for(i=0; i<func[fid].label_list.fidnum; i++){
	      if(func[fid].switch_label == func[fid].label_list.labels[i].label){
		    for(j=0; j<func[fid].num_var + GlobalNum; j++)
		      func[fid].label_list.labels[i].VarInfo[j] = func[fid].label_list.labels[i].VarInfo[j] & (init[j] & func[fid].switch_var[j]);
		  }
		  break;
		}
	  }
	  func[fid].in_switch = false;
	  break;
	}
	case INDIRECT_REF:
	  Traverse(TREE_OPERAND(node, 0), fid, init);
	  break;
	case RETURN_EXPR:
	{
      tree tmp = TREE_OPERAND(node, 0);
      if(tmp){
        if (TREE_CODE(tmp) == MODIFY_EXPR){
          Traverse(TREE_OPERAND(tmp, 1), fid, init);
        }
        else
          Traverse(tmp, fid, init);
      }
	  break;
	}
	case NOP_EXPR:
	  Traverse(TREE_OPERAND(node, 0), fid, init);
	  break;  
	case ADDR_EXPR:
    Traverse(TREE_OPERAND(node, 0), fid, init);
    break;
	case PARM_DECL:
	case VAR_DECL:
    {
	  if(VarInUse){
	    UseVar(IDENTIFIER_POINTER(DECL_NAME(node)), fid, init);
	  }	
	  else{
	    DefVar(IDENTIFIER_POINTER(DECL_NAME(node)), fid, init);
	  }
	  break;
	}	 
	case COND_EXPR:
    {
	  Traverse(TREE_OPERAND(node, 0), fid, init);
	  bool left[20], right[20];
	  int i;
	  for(i=0; i<func[fid].num_var; i++){
	    left[i] = init[i];
		right[i] = init[i];
	  }
	  printf("\n");
	  Traverse(TREE_OPERAND(node, 1), fid, left);
	  for(i=0; i<func[fid].num_var; i++){
	    left[i] = left[i] | init[i];
	  }
	  if(TREE_OPERAND(node, 2)){
	    Traverse(TREE_OPERAND(node, 2), fid, right);
		for(i=0; i<func[fid].num_var; i++){
		  right[i] = right[i] | init[i];
		}
	  }
	  for(i=0; i<func[fid].num_var; i++){
	    init[i] = left[i] & right[i];
	  }
	  break;
	}
    case MULT_EXPR:
    case PLUS_EXPR: 
    case MINUS_EXPR:
    case TRUNC_DIV_EXPR:
    case RDIV_EXPR:
    case EXACT_DIV_EXPR:
    case TRUTH_AND_EXPR:
    case TRUTH_ANDIF_EXPR:
    case TRUTH_OR_EXPR:
    case TRUTH_ORIF_EXPR:
    case LT_EXPR:
    case LE_EXPR:
    case GT_EXPR:
    case GE_EXPR:
    case EQ_EXPR:
    case NE_EXPR:	
	{
	  VarInUse = true;
	  tree left = TREE_OPERAND(node, 0);
	  tree right = TREE_OPERAND(node, 1);
	  Traverse(left, fid, init);
	  Traverse(right, fid, init);
	  break;
	}
	case COMPONENT_REF:
	{
	  tree op0 = TREE_OPERAND(node, 0);
	  tree op1 = TREE_OPERAND(node, 1);
	  Traverse(op0, fid, init);
	  Traverse(op1, fid, init);
	  break;
	}
	case CASE_LABEL_EXPR:
	{
	  int i;
	  if(CASE_LOW(node)){
	    if(func[fid].switch_goto){
		  for(i=0; i<func[fid].num_var + GlobalNum; i++){
		    func[fid].switch_var[i] = func[fid].fid_var[i];
			init[i] = func[fid].fid_var[i];
		  }
		}
		else{
	      for(i=0; i<func[fid].num_var + GlobalNum; i++){
		    func[fid].switch_var[i] = init[i];
		    init[i] = func[fid].fid_var[i];
		  }
		}
		Traverse(CASE_LOW(node), fid, init);
      }
	  else{
	    for(i=0; i<func[fid].num_var + GlobalNum; i++){
		  func[fid].switch_var[i] = init[i];
		  init[i] = func[fid].fid_var[i];
		}
	  }
	  break;
	}
	case MODIFY_EXPR:
	  if(TREE_CODE(TREE_OPERAND(node, 0)) != RESULT_DECL){
	    if(TREE_CODE(TREE_OPERAND(node, 0)) == VAR_DECL || TREE_CODE(TREE_OPERAND(node, 0)) == INDIRECT_REF || TREE_CODE(TREE_OPERAND(node, 0)) == PARM_DECL)
	      VarInUse = false;
			else
				VarInUse = true;
				Traverse(TREE_OPERAND(node, 0), fid, init);
	  }
	  VarInUse = true;
	  Traverse(TREE_OPERAND(node, 1), fid, init);
	  break;
	case INTEGER_CST:
	  break;
	case REAL_CST:
	  break;
	case CONSTRUCTOR:
	{
	  unsigned HOST_WIDE_INT ix;
	  tree field, val;
		bool is_struct_init = false;
		bool is_array_init = false;
		double_int fididx = double_int_zero;
		if (TREE_CODE (TREE_TYPE (node)) == RECORD_TYPE
		 || TREE_CODE (TREE_TYPE (node)) == UNION_TYPE)
			is_struct_init = true;
		else if (TREE_CODE (TREE_TYPE (node)) == ARRAY_TYPE
		 && TYPE_DOMAIN (TREE_TYPE (node))
		 && TYPE_MIN_VALUE (TYPE_DOMAIN (TREE_TYPE (node)))
		 && TREE_CODE (TYPE_MIN_VALUE (TYPE_DOMAIN (TREE_TYPE (node))))
		    == INTEGER_CST)
	  {
	    tree minv = TYPE_MIN_VALUE (TYPE_DOMAIN (TREE_TYPE (node)));
	    is_array_init = true;
	    fididx = tree_to_double_int (minv);
	  }	  
	  FOR_EACH_CONSTRUCTOR_ELT (CONSTRUCTOR_ELTS(node), ix, field, val){
	    if(field){
		  if(is_struct_init)
		    Traverse(node, fid, init);
		  if(is_array_init)
		    Traverse(node, fid, init);
		}
	  }
	}
	case TRUTH_NOT_EXPR:
	  Traverse(TREE_OPERAND(node, 0), fid, init);
	  break;
	default: break;
  }
  return -1;
}

void OutputLocal(struct CallNode *node){
  if(NULL == node)
    return;
  int i, j;
  if(2 == node->dfsstatus){
    return;
  }
  if(0 == node->dfsstatus){
	int fnum = node->funID;
	int num = 0;
	for(i=0; i<func[fnum].num_var; i++){
	if(0 < func[fnum].var[i].usebfinit)
	  num++;
	}
	if(0 < num){
	fprintf(fp, "%s: ", func[fnum].name);
	for(i=1; i<=num; i++){
	  for(j=0; j<func[fnum].num_var; j++){
		if(i == func[fnum].var[j].usebfinit){
		  if(1 == i)
			fprintf(fp, "%s", func[fnum].var[j].name);
		  else
			fprintf(fp, ", %s", func[fnum].var[j].name);
		}
	  }
	}
	fprintf(fp, "\n");
	}
    node->dfsstatus = 1;
    OutputLocal(node);
    return;    
  }
  if(1 == node->dfsstatus){
    for(i=0; i<node->child; i++){
	  OutputLocal(node->list[i]);
	}
	node->dfsstatus = 2;
	node = node->parent;
	OutputLocal(node);
  }
}

void OutputGlobal(){
  int num = 0;
  int i, j;
  for(i=0; i<GlobalNum; i++){
    if(GloVar[i].usebfinit)
	  num++;
  }
  if(0 == num)
    return;
  fprintf(fp, "Global: ");
  for(i=1; i<=num; i++){
    for(j=0; j<GlobalNum; j++){
	  if(i == GloVar[j].usebfinit){
	    if(i == 1)
		  fprintf(fp, "%s", GloVar[j].name);
		else
		  fprintf(fp, ", %s", GloVar[j].name);
	  }
	}
  }
  fprintf(fp, "\n");
}
