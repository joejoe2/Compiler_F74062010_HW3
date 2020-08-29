/*	Definition section */
%{
    #include "common.h" //Extern variables that communicate with lex
    #define MAX_SYMBOL_NUM 32*5
    // #define YYDEBUG 1
    // int yydebug = 1;

    extern int yylineno;
    extern int yylex();
    extern FILE *yyin;
    extern int level, line;

    void yyerror (char const *s)
    {
        printf("error:%d: %s\n", yylineno, s);
    }

    
    struct symbol{	
		char type[10];//var type
        char name[10];//var name
		char e_type[10];//element type if var type is array
		int address,lineno;
	};
	struct symbol *symbol_table[MAX_SYMBOL_NUM];//symbol_table is a array
	int num = 0;//total num of vars , for address assingment

    /* Symbol table function - you can add new function if needed. */
    static void create_symbol();
    static int insert_symbol();
    static int lookup_symbol();
    static void dump_symbol();
    /* Global variables */
    bool HAS_ERROR = false;//error flag, for deciding whether to generate hw3.j
    FILE *fptr;//pointer for hw3.j
    int cmp=0;//label num counter
    int m=0;//holder for conditional label num_id
    int max=0;//counter for 
    int e=0;//holder for exit conditional label num_id

    #define MAXSTACK 100 
    int stack[MAXSTACK];//for nested conditional(for, if)
    int top=-1;
    int isEmpty();
    void push(int); 
    int pop();
%}

%error-verbose

/* Use variable or self-defined structure to represent
 * nonterminal and token type
 */
%union {
    int i_val;
    float f_val;
    char* string;
    /* ... */
}

/* Token without return */
%token VAR
%token INT FLOAT BOOL STRING LAND LOR
%token NEWLINE
%token IF ELSE FOR INC DEC GEQ LEQ EQL NEQ ADD_ASSIGN SUB_ASSIGN MUL_ASSIGN QUO_ASSIGN REM_ASSIGN LAND LOR PRINT PRINTLN

/* Token with return, which need to sepcify type */
%token <string> INT_LIT
%token <string> FLOAT_LIT
%token <string> STRING_LIT
%token <string> BOOL_LIT
%token <string> identifier

/* Nonterminal with return, which need to sepcify type */
%type <string> Type TypeName ArrayType
%type <string> UnaryExpr add_op assign_op binary_op cmp_op mul_op unary_op Expression PrimaryExpr ConversionExpr IndexExpr Literal Operand logic_op
%type <string> p1 p2 p3 p4 p5

%left LOR LAND
/* Yacc will start at this nonterminal */
%start Program

/* Grammar section */
%%
//return type name in string from TypeName
Type
    : TypeName {$$=$1;}
;
//return type name in string
TypeName
    : INT {$$="int32";}
    | FLOAT {$$="float32";}
    | STRING {$$="string";}
    | BOOL {$$="bool";}
;

//precedence aware, for logic_op
Expression  
    : Expression logic_op Expression{
        int i;
        int j;
        int k;

        for(k=level;k>=0;k--){
            i=lookup_symbol($1, level);
            if(i!=-1)break;
        }
        for(k=level;k>=0;k--){
            j=lookup_symbol($3, level);
            if(j!=-1)break;
        }
        char t1[10];
        char t3[10];

        if(i==-1){
            strcpy(t1,$1);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
        }else{
            strcpy(t1,symbol_table[i]->type);
        }

        if(j==-1){
            strcpy(t3,$3);
        }else if(strcmp(symbol_table[j]->type,"array")==0){
            strcpy(t3,symbol_table[j]->e_type);
        }else{
            strcpy(t3,symbol_table[j]->type);
        }
        //t1 is left op's type, t3 is right op's type
        //may be identifier or literal or array, and try to find type of each
        
        
        //error when left or right op's type is not bool
        if(strcmp(t1,"bool")!=0){
            printf("error:%d: invalid operation: (operator %s not defined on %s)\n",line,$2,t1);
            HAS_ERROR=true;
        }else if(strcmp(t3,"bool")!=0){
            printf("error:%d: invalid operation: (operator %s not defined on %s)\n",line,$2,t3);
            HAS_ERROR=true;
        }
        
        //logic_op must return bool
        $$="bool";
        
        //print token        
        printf("%s\n",$2);

        //print IR
        if(strcmp($2, "LAND")==0){
            fprintf(fptr,"  iand\n");
        }else if(strcmp($2, "LOR")==0){
            fprintf(fptr,"  ior\n");
        }

    }
    |p1 {$$=$1;}
 ;    

//precedence aware, for cmp_op
 p1
    : p1 cmp_op p2{
        int i;
        int j;
        int k;

        for(k=level;k>=0;k--){
            i=lookup_symbol($1, k);
            if(i!=-1)break;
        }
        for(k=level;k>=0;k--){
            j=lookup_symbol($3, k);
            if(j!=-1)break;
        }

        char t1[10];
        char t3[10];

        if(i==-1){
            strcpy(t1,$1);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
        }else{
            strcpy(t1,symbol_table[i]->type);
        }

        if(j==-1){
            strcpy(t3,$3);
        }else if(strcmp(symbol_table[j]->type,"array")==0){
            strcpy(t3,symbol_table[j]->e_type);
        }else{
            strcpy(t3,symbol_table[j]->type);
        }
        //t1 is left op's type, t3 is right op's type
        //may be identifier or literal or array, and try to find type of each

        //error when left or right op's type is not same
        if(strcmp(t1,t3)!=0){
            printf("error:%d: invalid operation: %s (mismatched types %s and %s)\n",line,$2,t1,t3);
            HAS_ERROR=true;
        }
        
        //cmp_op must return bool
        $$="bool";
        
        //print token
        printf("%s\n",$2);

        //print IR
        //support all cmp_op, but only for same type(int32 or float32)
        if(strcmp($2, "GTR")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  isub\n");
                fprintf(fptr,"  ifgt L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);

            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fcmpl\n");
                fprintf(fptr,"  ifgt L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }
        }else if(strcmp($2, "LSS")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  isub\n");

                fprintf(fptr,"  iflt L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fcmpl\n");

                fprintf(fptr,"  iflt L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }
        }else if(strcmp($2, "EQL")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  isub\n");

                fprintf(fptr,"  ifeq L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fcmpl\n");

                fprintf(fptr,"  ifeq L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }
        }else if(strcmp($2, "LEQ")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  isub\n");

                fprintf(fptr,"  ifle L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fcmpl\n");

                fprintf(fptr,"  ifle L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }
        }else if(strcmp($2, "GEQ")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  isub\n");

                fprintf(fptr,"  ifge L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fcmpl\n");

                fprintf(fptr,"  ifge L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }
        }else if(strcmp($2, "NEQ")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  isub\n");

                fprintf(fptr,"  ifne L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fcmpl\n");

                fprintf(fptr,"  ifne L_cmp_%d\n", cmp++);
                fprintf(fptr,"  iconst_0\n");//false
                fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
                fprintf(fptr,"L_cmp_%d:\n", cmp-2);
                fprintf(fptr,"  iconst_1\n");//true
                fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            }
        }
    }
    |p2 {$$=$1;}
;

//precedence aware, for add_op
p2
    : p2 add_op p3{
        int i;
        int j;
        int k;

        for(k=level;k>=0;k--){
            i=lookup_symbol($1, k);
            if(i!=-1)break;
        }
        for(k=level;k>=0;k--){
            j=lookup_symbol($3, k);
            if(j!=-1)break;
        }

        char t1[10];
        char t3[10];

        if(i==-1){
            strcpy(t1,$1);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
        }else{
            strcpy(t1,symbol_table[i]->type);
        }

        if(j==-1){
            strcpy(t3,$3);
        }else if(strcmp(symbol_table[j]->type,"array")==0){
            strcpy(t3,symbol_table[j]->e_type);
        }else{
            strcpy(t3,symbol_table[j]->type);
        }
        //t1 is left op's type, t3 is right op's type
        //may be identifier or literal or array, and try to find type of each

        //error when left or right op's type is not same
        if(strcmp(t1,t3)!=0){
            printf("error:%d: invalid operation: %s (mismatched types %s and %s)\n",line,$2,t1,t3);
            HAS_ERROR=true;
        }

        //print token
        printf("%s\n",$2);

        //print IR
        //support all cmp_op, but only for same type(int32 or float32)
        if(strcmp($2, "ADD")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  iadd\n");
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fadd\n");
            }
        }else if(strcmp($2, "SUB")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  isub\n");
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fsub\n");
            }
        }

    }
    |p3 {$$=$1;}
;

//precedence aware, for mul_op
p3
    : p3 mul_op p4{
            int i;
            int j;
            int k;

            for(k=level;k>=0;k--){
                i=lookup_symbol($1, k);
                if(i!=-1)break;
            }
            for(k=level;k>=0;k--){
                j=lookup_symbol($3, k);
                if(j!=-1)break;
            }
            char t1[10];
            char t3[10];

            if(i==-1){
                strcpy(t1,$1);
            }else if(strcmp(symbol_table[i]->type,"array")==0){
                strcpy(t1,symbol_table[i]->e_type);
            }else{
                strcpy(t1,symbol_table[i]->type);
            }

            if(j==-1){
                strcpy(t3,$3);
            }else if(strcmp(symbol_table[j]->type,"array")==0){
                strcpy(t3,symbol_table[j]->e_type);
            }else{
                strcpy(t3,symbol_table[j]->type);
            }
        //t1 is left op's type, t3 is right op's type
        //may be identifier or literal or array, and try to find type of each

        //error when left or right op's type is not int32, for rem only
        if(strcmp($2,"REM")==0){
            if(strcmp(t1,"int32")!=0){
                printf("error:%d: invalid operation: (operator %s not defined on %s)\n",line,$2,t1);
                HAS_ERROR=true;
            }else if(strcmp(t3,"int32")!=0){
                printf("error:%d: invalid operation: (operator %s not defined on %s)\n",line,$2,t3);
                HAS_ERROR=true;
            }
        }else if(strcmp(t1,t3)!=0){
            //error when left or right op's type is not same
            printf("error:%d: invalid operation: %s (mismatched types %s and %s)\n",line,$2,t1,t3);
            HAS_ERROR=true;
        }

        //print token
        printf("%s\n",$2);

        //print IR
        //support all mul_op, but only for same type(int32 or float32)
        if(strcmp($2, "MUL")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  imul\n");
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fmul\n");
            }
        }else if(strcmp($2, "QUO")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  idiv\n");
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fdiv\n");
            }
        }else if(strcmp($2, "REM")==0){
            fprintf(fptr,"  irem\n");
            
        }
    }
    |p4 {$$=$1;}
;
// precedence aware,for UnaryExpr( unary or () or indexing), with return type in string
p4
    :UnaryExpr {$$=$1;}
;

//for unary or () or indexing, with return type in string
UnaryExpr
    : PrimaryExpr {$$=$1;}
    | unary_op UnaryExpr {
        $$=$2;
        
        //print token
        printf("%s\n",$1);

        //print IR
        //for - and !, without error check not in tests
        if(strcmp($1,"NEG")==0){
            if(strcmp($2,"int32")==0){
                fprintf(fptr,"  ineg\n");
            }else if(strcmp($2,"float32")==0){
                fprintf(fptr,"  fneg\n");
            }
        }else if(strcmp($1,"NOT")==0){
            fprintf(fptr,"  dup\n");
            fprintf(fptr,"  ixor\n");
        }
    }
;

//return op name
logic_op
    : LAND {$$="LAND";}
    | LOR {$$="LOR";}
;

//return op name
cmp_op
    : EQL {$$="EQL";}
    | NEQ {$$="NEQ";}
    | '<' {$$="LSS";}
    | LEQ {$$="LEQ";}
    | '>' {$$="GTR";}
    | GEQ {$$="GEQ";}
;

//return op name
add_op
    : '+' {$$="ADD";}
    | '-' {$$="SUB";}
;

//return op name
mul_op
    :'*' {$$="MUL";}
    | '/' {$$="QUO";}
    | '%' {$$="REM";}
;

//return op name
unary_op
    :'+' {$$="POS";}
    | '-' {$$="NEG";}
    | '!' {$$="NOT";}
;

//init 
Program
    : StatementList
;

//for Operand or indexing or ConversionExpr, with return type in string
PrimaryExpr
    : Operand {
        $$=$1;
    }
    | IndexExpr {$$=$1;}
    | ConversionExpr {$$=$1;}
;

//for array accessing, with return type in string
//always at the rhs of =, must load element
IndexExpr
    : PrimaryExpr '[' Expression ']'{
        //look up
        int i,index;
        for (i=level;i>=0;i--){
            index=lookup_symbol($1,i);
            if(index!=-1&&strcmp(symbol_table[index]->type,"array")==0){
                $$=symbol_table[index]->e_type;
                break;
            }
        }
        $$=$1;//return element type
        
        //not in tests
        //if(index==-1)
        //    printf("%s not declared\n", $1);

        //print IR
        //only for int32 or float32 array in tests
        if(index!=-1&&strcmp(symbol_table[index]->type,"array")==0){
            fprintf(fptr,"  aload %d\n", symbol_table[index]->address);  
            fprintf(fptr, "  swap\n");
            //array index will come first before, so need swap

            //load element
            if(strcmp(symbol_table[index]->e_type,"int32")==0){
                fprintf(fptr, "  iaload\n");
            }else if(strcmp(symbol_table[index]->e_type,"float32")==0){
                fprintf(fptr, "  faload\n");
            }
        }

    }
;
//for cast, with return type in string
ConversionExpr
    : Type '(' Expression ')' {
        $$=$1;

        //print IR
        //only for f2i or i2f in tests, without error check
        if(strcmp($1,"int32")==0){
            printf("F to I\n");
            fprintf(fptr, "f2i\n");
        }else{
            printf("I to F\n");
            fprintf(fptr, "i2f\n");
        }
    }
;

//for single identifier or literal or (), with return type in string
//assume to load
Operand
    : Literal {$$=$1;}
    | identifier {
        $$=$1;
        //look up and print
        int i=-1,index;
        for (i=level;i>=0;i--){
            index=lookup_symbol($1,i);
            if(index!=-1){
                printf("IDENT (name=%s, address=%d)\n", symbol_table[index]->name, symbol_table[index]->address);
                break;
            }
        }

        //error check
        if(index==-1){
            printf("error:%d: undefined: %s\n", line+1, $1);
            HAS_ERROR=true;
        }
            
        //print IR
        //load var not, include array
        if(strcmp(symbol_table[index]->type,"int32")==0){
            fprintf(fptr, "  iload %d\n", symbol_table[index]->address);
        }else if(strcmp(symbol_table[index]->type,"float32")==0){
            fprintf(fptr, "  fload %d\n", symbol_table[index]->address);
        }else if(strcmp(symbol_table[index]->type,"string")==0){
            fprintf(fptr, "  aload %d\n", symbol_table[index]->address);
        }else if(strcmp(symbol_table[index]->type,"bool")==0){
            fprintf(fptr, "  iload %d\n", symbol_table[index]->address);
        }
    }

        
    | '(' Expression ')' {$$=$2;}
;

//with return type in string, print token and IR
Literal
    : INT_LIT {$$="int32";printf("INT_LIT %s\n",$1);
    fprintf(fptr,"  ldc %s\n",$1);}
    | FLOAT_LIT {$$="float32";printf("FLOAT_LIT %.6f\n", atof($1));
    fprintf(fptr,"  ldc %s\n",$1);}
    | BOOL_LIT {$$="bool";printf("%s\n",$1);

        if(strcmp($1,"TRUE")==0){
            fprintf(fptr,"  iconst_1\n");
        }else{
            fprintf(fptr,"  iconst_0\n");
        }
    }
    | '"' STRING_LIT '"' {$$="string";printf("STRING_LIT %s\n",$2);
    fprintf(fptr,"  ldc \"%s\"\n",$2);
    }
;

//split by lines
StatementList
    : Statement StatementList 
    | Statement
;

//diff stmt
Statement
    : DeclarationStmt NEWLINE 
    | SimpleStmt NEWLINE 
    | Block NEWLINE 
    | IfStmt NEWLINE 
    | {
        //pre action for for-loop but useless in ..;..;.. and will be adjust back
        m=++max;
        push(m);
        fprintf(fptr,"L_cond_%d:\n", m);
    }ForStmt NEWLINE 
    | PrintStmt NEWLINE 
    | NEWLINE 
;
SimpleStmt
    : AssignmentStmt
    | ExpressionStmt
    | IncDecStmt
;

DeclarationStmt
    : VAR identifier Type{
        
        int index=lookup_symbol($2,level);
        if(index==-1){
            index = insert_symbol($2, $3, "-", level, 0);
        }else{
            printf("error:%d: %s redeclared in this block. previous declaration at line %d\n",line, $2, symbol_table[index]->lineno);
            HAS_ERROR=true;
        }
        //check redeclared and insert to symbol_table
        //print IR
        //with init to 0
        if(strcmp($3,"int32")==0){
            fprintf(fptr, " ldc 0\n");
            fprintf(fptr,"  istore %d\n", symbol_table[index]->address);
        }else if(strcmp($3,"float32")==0){
            fprintf(fptr, " ldc 0.0\n");
            fprintf(fptr,"  fstore %d\n", symbol_table[index]->address);
        }else if(strcmp($3,"string")==0){
            fprintf(fptr, " ldc \"\"\n");
            fprintf(fptr,"  astore %d\n", symbol_table[index]->address);
        }else if(strcmp($3,"bool")==0){
            fprintf(fptr, " ldc 0\n");
            fprintf(fptr,"  istore %d\n", symbol_table[index]->address);
        }
    }
    | VAR identifier Type '=' Expression{
        
        int index=lookup_symbol($2,level);
        if(index==-1){
            index = insert_symbol($2, $3, "-", level, 0);
        }else{
            printf("error:%d: %s redeclared in this block. previous declaration at line %d\n",line, $2, symbol_table[index]->lineno);
            HAS_ERROR=true;
        }
        //check redeclared and insert to symbol_table
        //print IR
        //with assign
        if(strcmp($3,"int32")==0){
            fprintf(fptr,"  istore %d\n", symbol_table[index]->address);
        }else if(strcmp($3,"float32")==0){
            fprintf(fptr,"  fstore %d\n", symbol_table[index]->address);
        }else if(strcmp($3,"string")==0){
            fprintf(fptr,"  astore %d\n", symbol_table[index]->address);
        }else if(strcmp($3,"bool")==0){
            fprintf(fptr,"  istore %d\n", symbol_table[index]->address);
        }
    }
    | VAR identifier '[' Expression ']' Type{
        int index=lookup_symbol($2,level);
        
        if(index==-1){
            index = insert_symbol($2, "array", $6, level, 1);
        }else{
            printf("error:%d: %s redeclared in this block. previous declaration at line %d\n",line, $2, symbol_table[index]->lineno);
            HAS_ERROR=true;
        }
        //check redeclared and insert to symbol_table
        //print IR
        //only for int32 or float32 array in tests
        if(strcmp($6,"int32")==0){
            fprintf(fptr,"  newarray int\n");
            fprintf(fptr,"  astore %d\n", symbol_table[index]->address);
        }else if(strcmp($6,"float32")==0){
            fprintf(fptr,"  newarray float\n");
            fprintf(fptr,"  astore %d\n", symbol_table[index]->address);
        }

        
    }
;

//
AssignmentStmt
    :identifier '[' Expression ']' assign_op{//for int32 index, without error check not in tests
        //look up
        
        int i,index;
        for (i=level;i>=0;i--){
            index=lookup_symbol($1,i);
            if(index!=-1&&strcmp(symbol_table[index]->type,"array")==0){
                //$$=symbol_table[index]->e_type;
                break;
            }
        }
        //not in tests
        //if(index==-1)
        //    printf("%s not declared\n", $1);


        //print IR
        //accessing array element
        if(index!=-1&&strcmp(symbol_table[index]->type,"array")==0){
            fprintf(fptr,"  aload %d\n", symbol_table[index]->address);  
            fprintf(fptr, "  swap\n");
            //index will come first, so need swap
        }

    } Expression{//only int index i tests
        //look up
        
        int i,index;
        for (i=level;i>=0;i--){
            index=lookup_symbol($1,i);
            if(index!=-1&&strcmp(symbol_table[index]->type,"array")==0){
                //$$=symbol_table[index]->e_type;
                break;
            }
        }
        //not in tests
        //if(index==-1)
        //    printf("%s not declared\n", $1);

        //print IR
        //store value to array element
        if(index!=-1&&strcmp(symbol_table[index]->type,"array")==0){
                if(strcmp(symbol_table[index]->e_type,"int32")==0){
                    fprintf(fptr,"  iastore\n");
                }else if(strcmp(symbol_table[index]->e_type,"float32")==0){
                    fprintf(fptr,"  fastore\n");
                }
            
        }

    }
    | Expression assign_op Expression{
        int i;
        int j;
        int k;

        for(k=level;k>=0;k--){
            i=lookup_symbol($1, k);
            if(i!=-1)break;
        }
        
        for(k=level;k>=0;k--){
            j=lookup_symbol($3, k);
            if(j!=-1)break;
        }
        char t1[10];
        char t3[10];

        if(i==-1){
            strcpy(t1,$1);
            //printf("error:%d: undefined: %s\n", line, $1);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
            
        }else{
            strcpy(t1,symbol_table[i]->type);
            
        }

        if(j==-1){
            strcpy(t3,$3);
        }else if(strcmp(symbol_table[j]->type,"array")==0){
            strcpy(t3,symbol_table[j]->e_type);
        }else{
            strcpy(t3,symbol_table[j]->type);
        }
        //t1 is left op's type, t3 is right op's type
        //may be identifier or literal or array, and try to find type of each

        //error check for ASSIGN in tests
        if(i!=-1&&strcmp($2,"ASSIGN")==0){
            if(strcmp(t1,t3)!=0){
                printf("error:%d: invalid operation: %s (mismatched types %s and %s)\n",line,$2,t1,t3);
                HAS_ERROR=true;
            }
        }

        //print token
        printf("%s\n", $2);

        //print IR
        //same type only without error checking
        if(strcmp($2,"ASSIGN")==0){
            //load var
            //load value <- will be consum by next line
            //store to addr <- here we are
            //so the fisrt line must be pop after store

            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  istore %d\n", symbol_table[i]->address);
                fprintf(fptr,"  pop\n");
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fstore %d\n", symbol_table[i]->address);
                fprintf(fptr,"  pop\n");
            }else if(strcmp(t1,"string")==0){
                fprintf(fptr,"  astore %d\n", symbol_table[i]->address);
                fprintf(fptr,"  pop\n");
            }else if(strcmp(t1,"bool")==0){
                fprintf(fptr,"  istore %d\n", symbol_table[i]->address);
                fprintf(fptr,"  pop\n");
            }
            
        }else if(strcmp($2,"ADD_ASSIGN")==0){
            //load var
            //load value <- will be consum by next line
            //apply operation to above two
            //store to addr

            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  iadd\n");
                fprintf(fptr,"  istore %d\n", symbol_table[i]->address);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fadd\n");
                fprintf(fptr,"  fstore %d\n", symbol_table[i]->address);
            }
            
        }else if(strcmp($2,"SUB_ASSIGN")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  isub\n");
                fprintf(fptr,"  istore %d\n", symbol_table[i]->address);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fsub\n");
                fprintf(fptr,"  fstore %d\n", symbol_table[i]->address);
            }
            
        }else if(strcmp($2,"MUL_ASSIGN")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  imul\n");
                fprintf(fptr,"  istore %d\n", symbol_table[i]->address);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fmul\n");
                fprintf(fptr,"  fstore %d\n", symbol_table[i]->address);
            }
            
        }else if(strcmp($2,"QUO_ASSIGN")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  idiv\n");
                fprintf(fptr,"  istore %d\n", symbol_table[i]->address);
            }else if(strcmp(t1,"float32")==0){
                fprintf(fptr,"  fdiv\n");
                fprintf(fptr,"  fstore %d\n", symbol_table[i]->address);
            }
            
        }else if(strcmp($2,"REM_ASSIGN")==0){
            if(strcmp(t1,"int32")==0){
                fprintf(fptr,"  irem\n");
            }
            fprintf(fptr,"  istore %d\n", symbol_table[i]->address);
        }
    }
    | Literal assign_op Expression{//sepcial case for error check in tests
        printf("error:%d: cannot assign to %s\n",line,$1);
        HAS_ERROR=true;
        printf("%s\n", $2);
    }
;

//return op name
assign_op
    :'=' {$$="ASSIGN";}
    | ADD_ASSIGN {$$="ADD_ASSIGN";}
    | SUB_ASSIGN {$$="SUB_ASSIGN";}
    | MUL_ASSIGN {$$="MUL_ASSIGN";}
    | QUO_ASSIGN {$$="QUO_ASSIGN";}
    | REM_ASSIGN {$$="REM_ASSIGN";}
;
ExpressionStmt
    : Expression
;

//++ or -- stmt
IncDecStmt
    : Expression INC {printf("INC\n");
        int i;
        int k;

        for(k=level;k>=0;k--){
            i=lookup_symbol($1, k);
            if(i!=-1)break;
        }
        char t1[10];
        char t3[10];

        if(i==-1){
            strcpy(t1,$1);
            //printf("error:%d: undefined: %s\n", line, $1);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
        }else{
            strcpy(t1,symbol_table[i]->type);
        }
        //t1 is op's type
        //may be identifier or literal or array, and try to find type of each
      
      //print IR
      //not support array not in tests
      if(strcmp(t1,"int32")==0){
          fprintf(fptr,"  ldc 1\n");
          fprintf(fptr,"  iadd\n");
          fprintf(fptr, "  istore %d\n",symbol_table[i]->address);
      }else if(strcmp(t1,"float32")==0){
          fprintf(fptr,"  ldc 1.0\n");
          fprintf(fptr,"  fadd\n");
          fprintf(fptr, "  fstore %d\n",symbol_table[i]->address);
      }

      
      
    }
    | Expression DEC {printf("DEC\n");
        int i;
        int k;

        for(k=level;k>=0;k--){
            i=lookup_symbol($1, k);
            if(i!=-1)break;
        }
        char t1[10];
        char t3[10];

        if(i==-1){
            strcpy(t1,$1);
            //printf("error:%d: undefined: %s\n", line, $1);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
        }else{
            strcpy(t1,symbol_table[i]->type);
        }


      if(strcmp(t1,"int32")==0){
          fprintf(fptr,"  ldc 1\n");
          fprintf(fptr,"  isub\n");
          fprintf(fptr, "  istore %d\n",symbol_table[i]->address);
      }else if(strcmp(t1,"float32")==0){
          fprintf(fptr,"  ldc 1.0\n");
          fprintf(fptr,"  fsub\n");
          fprintf(fptr, "  fstore %d\n",symbol_table[i]->address);
      }
    }
;
Block
    : '{' StatementList '}'{
        //dump
        dump_symbol(level+1);
    }
;

//pre action for conditional label for if,else if
pre:{
        m=++max;
        push(m);
        fprintf(fptr,"L_cond_%d:\n", m);
    };
IfStmt
    : pre IF Condition Block{
        m=pop();
        if(e==0)
            e = m;
        
        fprintf(fptr,"  goto L_exit_%d\n", e);
        fprintf(fptr,"L_iff_%d:\n", m);
        fprintf(fptr,"L_exit_%d:\n", e);
        e=0;
    }
    | pre IF Condition Block {
        m=pop();
        if(e==0)
            e=m;

        
        fprintf(fptr,"  goto L_exit_%d\n", e);
        fprintf(fptr,"L_iff_%d:\n", m);
        
    } ELSE IfStmt{
             
    }
    |Block{
        fprintf(fptr,"  goto L_exit_%d\n", e);
        fprintf(fptr,"L_exit_%d:\n", e);
        e=0;
    }
;

Condition
    :Expression {
        int i;
        int k;

        for(k=level;k>=0;k--){
            i=lookup_symbol($1, k);
            if(i!=-1)break;
        }

        char t1[10];

        if(i==-1){
            strcpy(t1,$1);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
        }else{
            strcpy(t1,symbol_table[i]->type);
        }
        
        if(strcmp($1,"bool")!=0){
            printf("error:%d: non-bool (type %s) used as for condition\n",line+1,t1);
            HAS_ERROR=true;
        }

        //after Condition Expression, test ture or false,goto label
        m=stack[top];
        fprintf(fptr,"  ifeq L_iff_%d\n", m);
        fprintf(fptr,"  goto L_ift_%d\n", m);
        fprintf(fptr,"L_ift_%d:\n", m);
        
        
        //if true do ...
    }
;

ForStmt
    :FOR Condition Block {
        //ex
        /*
        L_cond_1:
        ........
        if ture do Block else goto L_iff_1 
        goto L_cond_1
        L_iff_1:
        .....exit
        */
        m=pop();
        if(e==0)
            e=m;
        
        fprintf(fptr,"  goto L_cond_%d\n", m);
        fprintf(fptr,"L_iff_%d:\n", m);
        
    }
    |FOR SimpleStmt{
        //ex
        /*
        L_cond_1:
        is useless
        
        init here
        L_cond_2:
        .........
        if ture do goto L_iftdo_2  else goto L_iff_2
        L_iftpost_2:
        ....
        goto L_cond_2
        L_iftdo_2:
        ..........
        goto L_iftpost_2
        L_iff_2:
        .....exit
        */


        pop();//init stmt not conditional
    } ';' {//real conditional label
        m=++max;
        push(m);
        fprintf(fptr,"L_cond_%d:\n", m);
    }Condition {
        //goto if true do label
        fprintf(fptr,"  goto L_iftdo_%d\n", m);
    } ';' {
        //post label
        fprintf(fptr,"L_iftpost_%d:\n", m);
    }
    SimpleStmt {
        //after post action, loop back to conditional label
        fprintf(fptr,"  goto L_cond_%d\n", m);

        //below is if true do label
        fprintf(fptr,"L_iftdo_%d:\n", m);
    } Block{
        m=pop();
        if(e==0)
            e=m;
        
        fprintf(fptr,"  goto L_iftpost_%d\n", m);
        fprintf(fptr,"L_iff_%d:\n", m);
        
    }
;


InitStmt
    : SimpleStmt
;
PostStmt
    : SimpleStmt
;
PrintStmt
    : PRINT '(' Expression ')' {
        int i,j=level;
        for(j=level;j>=0;j--){
            i = lookup_symbol($3, j);
            if(i!=-1){
                break;
            }
        }
        char t1[10];

        if(i==-1){
            strcpy(t1,$3);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
        }else{
            strcpy(t1,symbol_table[i]->type);
        }

        printf("PRINT %s\n",t1);

        if(strcmp(t1,"int32")==0){
            fprintf(fptr,"  getstatic java/lang/System/out Ljava/io/PrintStream;\n");
            fprintf(fptr,"  swap\n");
            fprintf(fptr,"  invokevirtual java/io/PrintStream/print(I)V\n");
        }else if(strcmp(t1,"float32")==0){
            fprintf(fptr,"  getstatic java/lang/System/out Ljava/io/PrintStream;\n");
            fprintf(fptr,"  swap\n");
            fprintf(fptr,"  invokevirtual java/io/PrintStream/print(F)V\n");
        }if(strcmp(t1,"string")==0){
            fprintf(fptr,"  getstatic java/lang/System/out Ljava/io/PrintStream;\n");
            fprintf(fptr,"  swap\n");
            fprintf(fptr,"  invokevirtual java/io/PrintStream/print(Ljava/lang/String;)V\n");
        }if(strcmp(t1,"bool")==0){
            fprintf(fptr,"  ifne L_cmp_%d\n", cmp++);
            fprintf(fptr,"  ldc \"false\"\n");
            fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
            fprintf(fptr,"L_cmp_%d:\n", cmp-2);
            fprintf(fptr,"  ldc \"true\"\n");
            fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            fprintf(fptr,"  getstatic java/lang/System/out Ljava/io/PrintStream;\n");
            fprintf(fptr,"  swap\n");
            fprintf(fptr,"  invokevirtual java/io/PrintStream/print(Ljava/lang/String;)V\n");
        }
    }
    | PRINTLN '(' Expression ')' {
        
        int i,j=level;
        for(j=level;j>=0;j--){
            i = lookup_symbol($3, j);
            if(i!=-1){
                break;
            }
        }
        char t1[10];

        if(i==-1){
            strcpy(t1,$3);
        }else if(strcmp(symbol_table[i]->type,"array")==0){
            strcpy(t1,symbol_table[i]->e_type);
        }else{
            strcpy(t1,symbol_table[i]->type);
        }

        printf("PRINTLN %s\n",t1);

        if(strcmp(t1,"int32")==0){
            fprintf(fptr,"  getstatic java/lang/System/out Ljava/io/PrintStream;\n");
            fprintf(fptr,"  swap\n");
            fprintf(fptr,"  invokevirtual java/io/PrintStream/println(I)V\n");
        }else if(strcmp(t1,"float32")==0){
            fprintf(fptr,"  getstatic java/lang/System/out Ljava/io/PrintStream;\n");
            fprintf(fptr,"  swap\n");
            fprintf(fptr,"  invokevirtual java/io/PrintStream/println(F)V\n");
        }if(strcmp(t1,"string")==0){
            fprintf(fptr,"  getstatic java/lang/System/out Ljava/io/PrintStream;\n");
            fprintf(fptr,"  swap\n");
            fprintf(fptr,"  invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V\n");
        }if(strcmp(t1,"bool")==0){
            fprintf(fptr,"  ifne L_cmp_%d\n", cmp++);
            fprintf(fptr,"  ldc \"false\"\n");
            fprintf(fptr,"  goto L_cmp_%d\n", cmp++);
            fprintf(fptr,"L_cmp_%d:\n", cmp-2);
            fprintf(fptr,"  ldc \"true\"\n");
            fprintf(fptr,"L_cmp_%d:\n", cmp-1);
            fprintf(fptr,"  getstatic java/lang/System/out Ljava/io/PrintStream;\n");
            fprintf(fptr,"  swap\n");
            fprintf(fptr,"  invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V\n");
        }
    }
;




%%

/* C code section */
int main(int argc, char *argv[])
{
    create_symbol();

    if (argc == 2) {
        yyin = fopen(argv[1], "r");
    } else {
        yyin = stdin;
    }

    fptr = fopen("hw3.j","w");
    fprintf(fptr,".source hw3.j\n.class public Main\n.super java/lang/Object\n.method public static main([Ljava/lang/String;)V\n.limit stack 100 ; Define your storage size.\n.limit locals 100 ; Define your local space number.\n; ... Your generated Jasmin code for the input μGO program ...\n");

    fprintf(fptr,"m_%d:\n", m++);
    
    yylineno = 0;
    yyparse();
    dump_symbol(level);
	printf("Total lines: %d\n", yylineno);
    fclose(yyin);

    fprintf(fptr,"\nreturn\n.end method\n");
    fclose(fptr);
    if (HAS_ERROR) {
        remove("hw3.j");
    }
    return 0;
}

static void create_symbol() {
    int i;
	for(i = 0;i<MAX_SYMBOL_NUM; i++){
		symbol_table[i] = malloc(sizeof(struct symbol));
        strcpy(symbol_table[i]->name,"-");
        strcpy(symbol_table[i]->type,"-");
        symbol_table[i]->address=-1;
        symbol_table[i]->lineno=-1;
        strcpy(symbol_table[i]->e_type,"-");
	}
}

static int insert_symbol(char *s,char* t,char* e, int l, int dep) {
    int i;
    for(i = 32*l;i<32*(l+1); i++){
        if(symbol_table[i]->lineno==-1)break;
    }
    symbol_table[i]->address=num++;
    symbol_table[i]->lineno=line+dep;
    strcpy(symbol_table[i]->name,s);
    strcpy(symbol_table[i]->type, t);
    strcpy(symbol_table[i]->e_type,e);

    printf("> Insert {%s} into symbol table (scope level: %d)\n", s, l);

    return i;
}

static int lookup_symbol(char *s, int l) {
    int i;
    for(i = 32*l;i<32*(l+1); i++){
        if(strcmp(symbol_table[i]->name,s)==0)return i;
    }
    return -1;
}

static void dump_symbol(int l) {
    int i;
    printf("> Dump symbol table (scope level: %d)\n", l);
    printf("%-10s%-10s%-10s%-10s%-10s%s\n","Index", "Name", "Type", "Address", "Lineno", "Element type");
    //reset
    for(i = 32*l;i<32*(l+1); i++){
        if(symbol_table[i]->lineno==-1)break;
        
        printf("%-10d%-10s%-10s%-10d%-10d%s\n",i%32, symbol_table[i]->name, symbol_table[i]->type, symbol_table[i]->address, symbol_table[i]->lineno, symbol_table[i]->e_type);
        strcpy(symbol_table[i]->name,"-");
        strcpy(symbol_table[i]->type,"-");
        symbol_table[i]->address=-1;
        symbol_table[i]->lineno=-1;
        strcpy(symbol_table[i]->e_type,"-");
	}
}

int isEmpty(){
	if(top==-1){
		return 1; 
	}else{
		return 0;
	}
} 

void push(int data){
	if(top>=MAXSTACK){
		//printf("error\n");	
	}else{
		top++;
		stack[top]=data;
	}
 
} 

int pop(){
	int data;
	if(isEmpty()){
		//rintf("error\n");
	}else{
		data=stack[top];
		top--;
		return data; 
	}
}
