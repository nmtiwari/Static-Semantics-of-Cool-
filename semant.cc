

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

typedef SymbolTable<Symbol, SymData>& mySymboilTable;

/* create symbol table */

ClassTable::ClassTable(Classes classes)
: semant_errors(0) , error_stream(cerr) {
    m_class_symtable.enterscope();
    install_basic_classes();

    for ( int i = classes->first(); classes->more(i); i = classes->next(i) ) {
        class__class* class_ = static_cast<class__class*>(classes->nth(i));
        if ( m_class_symtable.probe(class_->getName()) ) {
            ostream& os = semant_error(class_);
            os << "Class " << class_->getName() << " was previously defined." << endl;
            continue;
        }
        m_class_symtable.addid(class_->getName(), new SymData(ClassType, class_, class_->getName()));
    }

    for ( int i = classes->first(); classes->more(i); i = classes->next(i) ) {
        class__class* class_ = static_cast<class__class*>(classes->nth(i));
        semant_class(class_);
    }

    SymData* class_symdata = m_class_symtable.probe(Main);
    if ( !class_symdata ) {
        ostream& os = semant_error();
        os << "Class Main is not defined." << endl;
    }
    else {
        if ( !class_symdata->m_class->getSymTable().probe(main_meth) ) {
            ostream& os = semant_error(class_symdata->m_class);
            os << "No 'main' method in class Main." << endl;
        }
    }

    for ( int i = classes->first(); classes->more(i); i = classes->next(i) ) {
        class__class* class_ = static_cast<class__class*>(classes->nth(i));
        semant_class_expr(class_);
    }

    m_class_symtable.exitscope();
}


/* From here onwards we are defining all the metods required to type check the program.
    There are seperate function for type checking the different exprssions and statements
    in the cool program
*/

/*
  This method is used to check the type semantics of the classes defined in the 
  cool program. In this section we check for the inheritance of the class. We make 
  sure that class does not inherit any primitive type or undefined class. We actually check
  the symbol table for the availablity of the parent class. If parent class is not defined in the
  symbol table the inheritance can not be legal type. Moreover we alos need to make sure that a class
  does not inherits itself 
*/
void ClassTable::semant_class(class__class* class_) {
    if ( class_->getName() != Object && class_->getName() != No_type ) {
        Symbol parent = class_->getParent();
        if ( parent == Bool || parent == Str || parent == SELF_TYPE ) {
            ostream& os = semant_error(class_);
            os << "Class " << class_->getName() << " cannot inherit class " << parent << "." << endl;
        }
        else if ( !m_class_symtable.probe(parent) ) {
            ostream& os = semant_error(class_);
            os << "Class " << class_->getName() << " inherits from an undefined class " << parent 
               << "." << endl;
        }
    }

    mySymboilTable symtable = class_->getSymTable();
    symtable.enterscope();
    Features features = class_->getFeatures();
    for ( int i = features->first(); features->more(i); i = features->next(i) ) {
        Feature feature = features->nth(i);
        if ( feature->getType() == AttrType ) {
            semant_attr(class_, feature);
        }
        else {
            semant_method(class_, feature);
        }
    }
}


/*
  This method is also used for type checking the semantics of the classes. Here we actually check the type 
  correctness of the attributes of the classes. Attribute checking requires us to check the type correctness of
  all the fields defined in the class along with the methods. 
  Here we traverse the AST in recursive manner to type check all the attribute.
*/
  
void ClassTable::semant_class_expr(class__class* class_) {
    Features features = class_->getFeatures();
    for ( int i = features->first(); features->more(i); i = features->next(i) ) {
        Feature feature = features->nth(i);
        if ( feature->getType() == AttrType ) {
            semant_attr_expr(class_, feature);
        }
        else {
            semant_method_expr(class_, feature);
        }
    }
}


/*
  This method is also used for type checking the semantics of the classes. Here we actually check the type 
  correctness of the attributes of the classes. Checks like each attribute is defined only once, there are
  no self type checking and then also that assignment of the attributes are done with same type or subtype. 
*/
  
void ClassTable::semant_attr(class__class* class_, Feature feature) {
    attr_class* attr = static_cast<attr_class*>(feature);
    Symbol attrname = attr->getName();
    mySymboilTable symtable = class_->getSymTable();
    if ( attrname == self ) {
        ostream& os = semant_error(class_);
        os << "'self' cannot be the name of an attribute." << endl;
    }
    else if ( symtable.probe(attrname) ) {
        ostream& os = semant_error(class_);
        os << "Attribute " << attrname << " is multiply defined in class." << endl;
    }

    Symbol declaretype = attr->getDeclareType();
    if ( !class_lookup(class_, declaretype) ) {
        ostream& os = semant_error(class_);
        os << "Class " << declaretype << " of attribute " << attrname << " is undefined." << endl;
    }

    symtable.addid(attr->getName(), new SymData(AttrType, class_, declaretype));
}


/*
  This method is also used for type checking the semantics of the attributes of the class. Here we actually check the type 
  correctness of the attributes of the parent classes. 
*/
  
void ClassTable::semant_attr_expr(class__class* class_, Feature feature) {
    attr_class* attr = static_cast<attr_class*>(feature);
    Symbol attrname = attr->getName();

    // check attr in parent
    if ( name_lookup(class_, attrname) ) {
        ostream& os = semant_error(class_);
        os << "Attribute " << attrname << " is an attribute of an inherited class."
           << endl;
        return;
    }

    semant_expression(class_, attr->getExpression());
}
/*
    Semantics of the method involves type checking for return type, argument, expressions and 
    then all statements (body) of the method. Following method is used for type checking that
    method is defined with correct return type, return type does exist. MOreover no field is defined multiple
    times in same method.
*/
void ClassTable::semant_method(class__class* class_, Feature feature) {
    method_class* method = static_cast<method_class*>(feature);
    Symbol methodname = method->getName();
    mySymboilTable symtable = class_->getSymTable();
    if ( symtable.probe(methodname) ) {
        ostream& os = semant_error(class_);
        os << "Method" << methodname << " is multiply defined." << endl;
        return;
    }

    Symbol returntype = method->getReturnType();
    if ( !class_lookup(class_, returntype) ) {
        returntype = No_type;
        ostream& os = semant_error(class_);
        os << "Undefined return type " << returntype << " in method " << methodname << "." << endl;
    }

    SymData* method_symdata = new SymData(MethodType, class_, returntype);

    symtable.enterscope();
    Formals formals = method->getFormals();
    for ( int i = formals->first(); formals->more(i); i = formals->next(i) ) {
        semant_formal(class_, method_symdata, static_cast<formal_class*>(formals->nth(i)));
    }
    symtable.exitscope();
    symtable.addid(methodname, method_symdata);
}


/*
    Overloading and overriding are two main concepts of the OOP. In this part of the 
    type check semantics takes care of the number of arguments, their type and return type
    in overloading and overriding the methods.
*/
void ClassTable::semant_method_expr(class__class* class_, Feature feature) {
    method_class* method = static_cast<method_class*>(feature);
    Symbol methodname = method->getName();

    Symbol returntype = method->getReturnType();
    if ( !class_lookup(class_, returntype) ) {
        returntype = No_type;
    }

    mySymboilTable symtable = class_->getSymTable();
    SymData* method_symdata = symtable.probe(methodname);
    if ( !method_symdata ) {
        return;
    }
    Formals formals = method->getFormals();
    if ( formals->len() != static_cast<int>(method_symdata->m_methodArg.size()) ) {
        return;
    }

    // check method in parent return type, argument number and argument type
    if ( SymData* parent_method_data = name_lookup(class_, methodname) ) {
        Symbol parent_method_type = parent_method_data->m_type;
        if ( parent_method_type != No_type && returntype != No_type && \
             parent_method_type != returntype ) {
            if ( !check_type(class_, returntype, parent_method_type) ) {
                ostream& os = semant_error(class_);
                return;
            }
        }
        else if ( method_symdata->m_methodArg.size() != parent_method_data->m_methodArg.size() ) {
            ostream& os = semant_error(class_);
            os << "Incompatible number of formal parameters in redefined method "
               << methodname << "." << endl;
            return;
        }
        else {
            for ( int i = 0; i < static_cast<int>(method_symdata->m_methodArg.size()) ; ++i ) {
                if ( method_symdata->m_methodType[i] != parent_method_data->m_methodType[i] ) {
                    ostream& os = semant_error(class_);
                    os << "In redefined method " << methodname << ", parameter type "
                       << method_symdata->m_methodType[i] << " is different from original type "
                       << parent_method_data->m_methodType[i] << endl;
                    return;
                }
            }
        }
    }

    symtable.enterscope();
    for ( int i = formals->first(); formals->more(i); i = formals->next(i) ) {
        semant_formal(class_, NULL, static_cast<formal_class*>(formals->nth(i)));
    }

    Expression expr = method->getExpression();
    semant_expression(class_, expr);

    if ( expr->type != No_type && returntype != No_type && expr->type != returntype ) {
        if ( !check_type(class_, expr->type, returntype) ) {
            ostream& os = semant_error(class_);
            os << "Inferred return type " << expr->type << " of method " << methodname 
               << " does not conform to declared return type " << returntype << "." << endl;
        }
    }
    symtable.exitscope();

}


/*
    Methods can not have multiple defined arguments and they can not even have self_type as argument of the
    function. We need to take care that all methods follow this rule of type semantics before we go in 
    code generation phase of compilation.
*/


void ClassTable::semant_formal(class__class* class_, SymData* method_symdata, formal_class* formal) {
    Symbol formalname = formal->getName();
    mySymboilTable symtable = class_->getSymTable();
    if ( formalname == self ) {
        ostream& os = semant_error(class_);
        os << "'self' cannot be the name of a formal parameter." << endl;
    }
    else if ( symtable.probe(formalname) ) {
        ostream& os = semant_error(class_);
        os << "Formal parameter " << formalname << " is multipley defined." << endl;
    }

    Symbol declaretype = formal->getDeclareType();
    if ( declaretype == SELF_TYPE ) {
        ostream& os = semant_error(class_);
        os << "Formal parameter " << formalname << " cannot have type SELF_TYPE." << endl;
    }
    else if ( !class_lookup(class_, declaretype) ) {
        ostream& os = semant_error(class_);
        os << "Class " << declaretype <<  " of formal parameter " << formalname << " is undefined." 
           << endl;
    }

    symtable.addid(formalname, new SymData(FormalType, class_, declaretype));
    if ( method_symdata ) {
        method_symdata->m_methodArg.push_back(formalname);
        method_symdata->m_methodType.push_back(declaretype);
    }
}

/*
    There are multiple expression types in cool and they have different semantics. We have defined a 
    function which takes care of the types checking of all the expression by switch case analysis.Cases of the switch statement involve : 
    AssignType
    StaticDispatchType
    DispatchType
    ObjectType
    IsVoidType
    NewType
    StringType
    BoolType
    IntType
    CompType
    LeqType
    EqType
    LtType
    NegType
    DivideType
    MulType
    SubType
    PlusType
    LetType
    BlockType
    CaseType
    LoopType
    CondType
*/
void ClassTable::semant_expression(class__class* class_, Expression expr) {
    // give expr default type
    expr->type = No_type;

    TreeType type = expr->getType();
    switch (type) {
        case AssignType:
            {
                assign_class* assign = static_cast<assign_class*>(expr);
                Symbol name = assign->getName();
                if ( name == self ) {
                    ostream& os = semant_error(class_);
                    os << "Cannot assign to 'self'." << endl;
                    return;
                }
                SymData* symdata = name_lookup(class_, name, true);
                if ( !symdata ) {
                    ostream& os = semant_error(class_);
                    os << "Assignment to undeclared variable " << name << "." << endl;
                }
                semant_expression(class_, assign->getExpression());
                Symbol ret_type = assign->getExpression()->type;
                if ( ret_type != No_type && \
                     symdata && symdata->m_type != No_type && ret_type != symdata->m_type ) {
                    ostream& os = semant_error(class_);
                    os << "Type " << ret_type << " of assigned expression does not confrom to "
                       << "declared type " << symdata->m_type << " of identifier " << name << "."
                       << endl;
                }
                expr->type = ret_type;
            }
            break;
        case StaticDispatchType:
            {
                static_dispatch_class* dispatch = static_cast<static_dispatch_class*>(expr);
                Expression dispatch_expr = dispatch->getExpression();
                semant_expression(class_, dispatch_expr);

                Symbol dispatch_type = dispatch->getTypeName();
                SymData* class_symdata = class_lookup(class_, dispatch_type);
                if ( !class_symdata ) {
                    ostream& os = semant_error(class_);
                    os << "Static dispatch to undefined class " << dispatch_type << endl;
                }
                else {
                    Symbol class_type = dispatch_expr->type;
                    if ( !check_type(class_, class_type, dispatch_type) ) {
                        ostream& os = semant_error(class_);
                        os << "Expression type " << class_type << " does not conform to declared "
                           << "static dispatch type " << dispatch_type << "." << endl;
                        return;
                    }
                }

                Symbol methodname = dispatch->getName();
                SymData* method_symdata = semant_dispatch(class_, class_symdata->m_class, methodname, 
                                                          expr, dispatch_expr);
                if ( !method_symdata ) {
                    return;
                }

                semant_dispatch_formal(class_, dispatch->getActual(), method_symdata, methodname);
            }
            break;
        case DispatchType:
            {
                dispatch_class* dispatch = static_cast<dispatch_class*>(expr);
                Expression dispatch_expr = dispatch->getExpression();
                semant_expression(class_, dispatch_expr);
                Symbol methodname = dispatch->getName();

                // SELF_TYPE
                SymData* class_symdata = class_lookup(class_, dispatch_expr->type);
                SymData* method_symdata = class_symdata->m_class->getSymTable().lookup(methodname);

                if ( method_symdata ) {
                    if ( method_symdata->m_type == SELF_TYPE ) {
                        expr->type = class_symdata->m_class->getName();
                    }
                    else {
                        expr->type = method_symdata->m_type;
                    }
                }
                else {
                    SymData* parent = m_class_symtable.lookup(class_->getParent());
                    method_symdata = semant_dispatch(class_, parent->m_class, methodname, expr, 
                                                     dispatch_expr);
                    if ( !method_symdata ) {
                        return;
                    }
                }

                semant_dispatch_formal(class_, dispatch->getActual(), method_symdata, methodname);
            }
            break;
        case CondType:
            {
                cond_class* cond = static_cast<cond_class*>(expr);
                Expression pred = cond->getPred();
                semant_expression(class_, pred);
                if ( pred->type != Bool ) {
                    ostream& os = semant_error(class_);
                    os << "Predicate of 'if ' does not have type Bool." << endl;
                }

                Expression then_expr = cond->getThen();
                semant_expression(class_, then_expr);
                Symbol then_type = then_expr->type;

                Expression else_expr = cond->getElse();
                semant_expression(class_, else_expr);
                Symbol else_type = else_expr->type;

                // find least upper bound
                expr->type = get_least_upper_bound(class_, then_type, else_type);
            }
            break;
        case LoopType:
            {
                loop_class* loop = static_cast<loop_class*>(expr);
                Expression pred = loop->getPred();
                semant_expression(class_, pred);
                if ( pred->type != Bool ) {
                    ostream& os = semant_error(class_);
                    os << "Loop condition does not have type Bool." << endl;
                }

                Expression body = loop->getBody();
                semant_expression(class_, body);
                // loop return type is Object
                expr->type = Object;
            }
            break;
        case CaseType:
            {
                typcase_class* typcase = static_cast<typcase_class*>(expr);
                Expression typexpr = typcase->getExpression();
                semant_expression(class_, typexpr);

                mySymboilTable symtable = class_->getSymTable();
                symtable.enterscope();
                Cases cases = typcase->getCases();
                for ( int i = cases->first(); cases->more(i); i = cases->next(i) ) {
                    Symbol branch_type = semant_branch(class_,
                                                       static_cast<branch_class*>(cases->nth(i)),
                                                       typexpr->type);
                    if ( i == 0 ) {
                        expr->type = branch_type;
                    }
                    else {
                        expr->type = get_least_upper_bound(class_, expr->type, branch_type);
                    }
                }
                symtable.exitscope();
            }
            break;
        case BlockType:
            {
                Expressions exprs = static_cast<block_class*>(expr)->getExpressions();
                for ( int i = exprs->first(); exprs->more(i); i = exprs->next(i) ) {
                    semant_expression(class_, exprs->nth(i));
                    expr->type = exprs->nth(i)->type;
                }
            }
            break;
        case LetType:
            {
                let_class* let = static_cast<let_class*>(expr);
                Symbol identifier = let->getIdentifier();
                if ( identifier == self ) {
                    ostream& os = semant_error(class_);
                    os << "'self' cannot be bound in a 'let' expression." << endl;
                    return;
                }

                Symbol declaretype = let->getDeclareType();
                if ( !class_lookup(class_, declaretype) ) {
                    ostream& os = semant_error(class_);
                    os << "Class " << declaretype << " of let-bound identifier " << identifier
                       << " is undefined." << endl;
                }

                Expression init = let->getInit();
                semant_expression(class_, init);
                if ( init->type != No_type && init->type != declaretype ) {
                    if ( !check_type(class_, init->type, declaretype) ) {
                        ostream& os = semant_error(class_);
                        os << "Inferred type " << init->type << " of initialization of " << identifier 
                           << " does not confrom to identifier's declared type " << declaretype << "."
                           << endl;
                    }
                }

                mySymboilTable symtable = class_->getSymTable();
                symtable.enterscope();
                symtable.addid(identifier, new SymData(LetType, class_, declaretype));
                Expression body = let->getBody();
                semant_expression(class_, body);
                symtable.exitscope();

                expr->type = body->type;
            }
            break;
        case PlusType:
            {
                plus_class* plus = static_cast<plus_class*>(expr);
                Expression expr1 = plus->getExpression1();
                semant_expression(class_, expr1);
                Expression expr2 = plus->getExpression2();
                semant_expression(class_, expr2);
                if ( expr1->type != Int || expr2->type != Int || expr1->type != expr2->type ) {
                    ostream& os = semant_error(class_);
                    os << "non-Int arguments: " << expr1->type << " + " << expr2->type << endl;
                }
                expr->type = Int;
            }
            break;
        case SubType:
            {
                sub_class* sub = static_cast<sub_class*>(expr);
                Expression expr1 = sub->getExpression1();
                semant_expression(class_, expr1);
                Expression expr2 = sub->getExpression2();
                semant_expression(class_, expr2);
                if ( expr1->type != Int || expr2->type != Int || expr1->type != expr2->type ) {
                    ostream& os = semant_error(class_);
                    os << "non-Int arguments: " << expr1->type << " - " << expr2->type << endl;
                }
                expr->type = Int;
            }
            break;
        case MulType:
            {
                mul_class* mul = static_cast<mul_class*>(expr);
                Expression expr1 = mul->getExpression1();
                semant_expression(class_, expr1);
                Expression expr2 = mul->getExpression2();
                semant_expression(class_, expr2);
                if ( expr1->type != Int || expr2->type != Int || expr1->type != expr2->type ) {
                    ostream& os = semant_error(class_);
                    os << "non-Int arguments: " << expr1->type << " * " << expr2->type << endl;
                }
                expr->type = Int;
            }
            break;
        case DivideType:
            {
                divide_class* divide = static_cast<divide_class*>(expr);
                Expression expr1 = divide->getExpression1();
                semant_expression(class_, expr1);
                Expression expr2 = divide->getExpression2();
                semant_expression(class_, expr2);
                if ( expr1->type != Int || expr2->type != Int || expr1->type != expr2->type ) {
                    ostream& os = semant_error(class_);
                    os << "non-Int arguments: " << expr1->type << " / " << expr2->type << endl;
                }
                expr->type = Int;
            }
            break;
        case NegType:
            {
                neg_class* neg = static_cast<neg_class*>(expr);
                Expression negexpr = neg->getExpression();
                semant_expression(class_, negexpr);
                if ( negexpr->type != Int ) {
                    ostream& os = semant_error(class_);
                    os << "Argument of '~' has type " << negexpr->type << " instead of Int." << endl;
                }
                expr->type = Int;
            }
            break;
        case LtType:
            {
                lt_class* lt = static_cast<lt_class*>(expr);
                Expression expr1 = lt->getExpression1();
                semant_expression(class_, expr1);
                Expression expr2 = lt->getExpression2();
                semant_expression(class_, expr2);
                if ( expr1->type != expr2->type ) {
                    ostream& os = semant_error(class_);
                    os << "non-Int arguments: " << expr1->type << " < " << expr2->type << endl;
                }
                expr->type = Bool;
            }
            break;
        case EqType:
            {
                eq_class* eq = static_cast<eq_class*>(expr);
                Expression expr1 = eq->getExpression1();
                semant_expression(class_, expr1);
                Expression expr2 = eq->getExpression2();
                semant_expression(class_, expr2);

                if ( expr1->type == Int || expr1->type == Bool || expr1->type == Str || \
                     expr2->type == Int || expr2->type == Bool || expr2->type == Str ) {
                    if ( expr1->type != expr2->type ) {
                        ostream& os = semant_error(class_);
                        os << "non-Int arguments: " << expr1->type << " = " << expr2->type << endl;
                    }
                }
                else {
                    SymData* symdata1 = class_lookup(class_, expr1->type);
                    SymData* symdata2 = class_lookup(class_, expr2->type);
                    if ( symdata1->m_treetype != ClassType || symdata2->m_treetype != ClassType ) {
                        ostream& os = semant_error(class_);
                        os << "non-Int arguments: " << expr1->type << " = " << expr2->type << endl;
                    }
                }
                expr->type = Bool;
            }
            break;
        case LeqType:
            {
                leq_class* leq = static_cast<leq_class*>(expr);
                Expression expr1 = leq->getExpression1();
                semant_expression(class_, expr1);
                Expression expr2 = leq->getExpression2();
                semant_expression(class_, expr2);
                if ( expr1->type != expr2->type ) {
                    ostream& os = semant_error(class_);
                    os << "non-Int arguments: " << expr1->type << " <= " << expr2->type << endl;
                }
                expr->type = Bool;
            }
            break;
        case CompType:
            {
                comp_class* comp = static_cast<comp_class*>(expr);
                Expression compexpr = comp->getExpression();
                semant_expression(class_, compexpr);
                if ( expr->type != No_type && expr->type != Bool ) {
                    ostream& os = semant_error(class_);
                    os << "Argument of 'not' has type " << expr->type << " instead of Bool." << endl;
                }
                expr->type = Bool;
            }
            break;
        case IntType:
            expr->type = Int;
            break;
        case BoolType:
            expr->type = Bool;
            break;
        case StringType:
            expr->type = Str;
            break;
        case NewType:
            {
                new__class* newclass = static_cast<new__class*>(expr);
                Symbol name = newclass->getTypeName();
                SymData* symdata = class_lookup(class_, name);
                if ( name == SELF_TYPE ) {
                    expr->type = SELF_TYPE;
                }
                else if ( !symdata ) {
                    ostream& os = semant_error(class_);
                    os << "'new' used with undefined class " << name << "." << endl;
                }
                else {
                    expr->type = symdata->m_type;
                }
            }
            break;
        case IsVoidType:
            {
                isvoid_class* isvoid = static_cast<isvoid_class*>(expr);
                Expression voidexpr = isvoid->getExpression();
                semant_expression(class_, voidexpr);
                expr->type = Bool;
            }
            break;
        case ObjectType:
            {
                object_class* object = static_cast<object_class*>(expr);
                Symbol name = object->getSymbol();
                if ( name == self ) {
                    expr->type = SELF_TYPE;
                }
                else {
                    SymData* symdata = name_lookup(class_, name, true);
                    if ( !symdata ) {
                        ostream& os = semant_error(class_);
                        os << "Undeclared identifier " << name << "." << endl;
                        expr->type = No_type;
                    }
                    else {
                        expr->type = symdata->m_type;
                    }
                }
            }
            break;
        case NoExpressionType:
        default:
            break;
        }
}

SymData* ClassTable::semant_dispatch(class__class* class_, class__class* now_class, Symbol methodname,
                                     Expression expr, Expression dispatch_expr) {
    while ( true ) {
        if ( !now_class ) {
            ostream& os = semant_error(class_);
            os << "Dispatch to undefined method " << methodname << "." << endl;
            return NULL;
        }
        SymData* method_symdata = now_class->getSymTable().lookup(methodname);
        if ( method_symdata ) {
            if ( method_symdata->m_type == SELF_TYPE ) {
                expr->type = dispatch_expr->type;
            }
            else {
                expr->type = method_symdata->m_type;
            }
            return method_symdata;
        }
        else {
            if ( now_class->getParent() != No_class ) {
                SymData* parent = m_class_symtable.lookup(now_class->getParent());
                now_class = parent->m_class;
            }
            else {
                ostream& os = semant_error(class_);
                os << "Dispatch to undefined method " << methodname << "." << endl;
                return NULL;
            }
        }
    }
    return NULL;
}

void ClassTable::semant_dispatch_formal(class__class* class_, Expressions actual,
                                        SymData* method_symdata, Symbol methodname) {
    if ( actual->len() != static_cast<int>(method_symdata->m_methodType.size()) ) {
        ostream& os = semant_error(class_);
        os << "Method " << methodname << " called with wrong number of arguments." << endl;
    }
    else {
        for ( int i = actual->first(); actual->more(i) ; i = actual->next(i) ) {
            semant_expression(class_, actual->nth(i));
            if ( actual->nth(i)->type != method_symdata->m_methodType[i] ) {
                if ( !check_type(class_, actual->nth(i)->type, method_symdata->m_methodType[i]) ) {
                    ostream& os = semant_error(class_);
                    os << "In call of method " << methodname << ", type " << actual->nth(i)->type
                       << " of parameter " << method_symdata->m_methodArg[i] << " does not conform to "
                       << "declared type " << method_symdata->m_methodType[i] << "." << endl;
                    break;
                }
            }
        }
    }
}

Symbol ClassTable::semant_branch(class__class* class_, branch_class* branch, Symbol case_type) {
    mySymboilTable symtable = class_->getSymTable();
    Symbol branch_name = branch->getName();
    Symbol branch_type = branch->getDeclareType();
    if ( symtable.probe(branch_type) ) {
        ostream& os = semant_error(class_);
        os << "Duplicate branch " << branch_type << " in case statement." << endl;
        return No_type;
    }

    symtable.addid(branch_name, new SymData(BranchNameType, class_, branch_type));
    symtable.addid(branch_type, new SymData(BranchTypeType, class_, branch_type));

    Expression branch_expr = branch->getExpression();
    semant_expression(class_, branch_expr);
    return branch_expr->type;
}

bool ClassTable::check_type(class__class* class_, Symbol now_type, Symbol correct_type) {
    SymData* class_symdata = class_lookup(class_, now_type);
    if ( class_symdata ) {
        if ( class_symdata->m_type == correct_type ) {
            return true;
        }
        for ( class__class* now_class = class_symdata->m_class; ; ) {
            Symbol parent = now_class->getParent();
            if ( parent == No_class ) {
                return false;
            }
            else if ( parent == correct_type ) {
                return true;
            }
            else {
                now_class = m_class_symtable.lookup(parent)->m_class;
            }
        }
    }
    else {
        return false;
    }
}

SymData* ClassTable::class_lookup(class__class* class_, Symbol child) {
    if ( child == SELF_TYPE ) {
        return m_class_symtable.lookup(class_->getName());
    }
    else {
        return m_class_symtable.lookup(child);
    }
}

Symbol ClassTable::get_least_upper_bound(class__class* class_, Symbol type1, Symbol type2) {
    if ( type1 == No_type || type2 == No_type ) {
        return No_type;
    }
    else if ( check_type(class_, type1, type2) ) {
        return type2;
    }
    else if ( check_type(class_, type2, type1) ) {
        return type1;
    }
    else {
        SymData* class_symdata = class_lookup(class_, type1);
        if ( class_symdata ) {
            for ( class__class* now_class = class_symdata->m_class; ; ) {
                Symbol parent = now_class->getParent();
                if ( parent == Object ) {
                    return parent;
                }
                else if ( check_type(class_, type2, parent) ) {
                    return parent;
                }
                else {
                    now_class = m_class_symtable.lookup(parent)->m_class;
                }
            }
        }
    }
    return No_type;
}

SymData* ClassTable::name_lookup(class__class* class_, Symbol name, bool check_current) {
    SymData* symdata = NULL;
    if ( check_current ) {
        symdata = class_->getSymTable().lookup(name);
        if ( symdata ) {
            return symdata;
        }
    }
    for ( class__class* now_class = class_; ; ) {
        if ( !now_class ) {
            break;
        }

        Symbol parent = now_class->getParent();
        if ( parent == No_class || parent == SELF_TYPE ) {
            break;
        }

        SymData* class_symdata = class_lookup(class_, parent);
        if ( !class_symdata ) {
            break;
        }

        mySymboilTable parent_symtable = class_symdata->m_class->getSymTable();
        symdata = parent_symtable.probe(name);
        if ( symdata ) {
            break;
        }
        else {
            now_class = class_symdata->m_class;
        }
    }
    return symdata;
}


void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    SymData* symdata = new SymData(ClassType, static_cast<class__class*>(Object_class), Object);
    m_class_symtable.addid(Object, symdata);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    symdata = new SymData(ClassType, static_cast<class__class*>(IO_class), IO);
    m_class_symtable.addid(IO, symdata);

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    symdata = new SymData(ClassType, static_cast<class__class*>(Int_class), Int);
    m_class_symtable.addid(Int, symdata);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    symdata = new SymData(ClassType, static_cast<class__class*>(Bool_class), Bool);
    m_class_symtable.addid(Bool, symdata);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);

    symdata = new SymData(ClassType, static_cast<class__class*>(Str_class), Str);
    m_class_symtable.addid(Str, symdata);

    // No_type
    Class_ No_type_class =
	class_(No_type, No_class, nil_Features(),filename);
    symdata = new SymData(ClassType, static_cast<class__class*>(No_type_class), No_type);
    m_class_symtable.addid(No_type, symdata);

    // prim_slot
    symdata = new SymData(ClassType, NULL, NULL);
    m_class_symtable.addid(prim_slot, symdata);

    // FIXME: self type
    symdata = new SymData(ClassType, NULL, NULL);
    m_class_symtable.addid(SELF_TYPE, symdata);

    // start to semant class content after all class names are defined
    semant_class(static_cast<class__class*>(Object_class));
    semant_class(static_cast<class__class*>(IO_class));
    semant_class(static_cast<class__class*>(Int_class));
    semant_class(static_cast<class__class*>(Bool_class));
    semant_class(static_cast<class__class*>(Str_class));
}


////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 



/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable *classtable = new ClassTable(classes);

    /* some semantic analysis code may go here */

    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }
}


