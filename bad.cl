(*
 *  This file shows how to implement a list data type for lists of integers.
 *  It makes use of INHERITANCE and DYNAMIC DISPATCH.
 *
 *  The List class has 4 operations defined on List objects. If 'l' is
 *  a list, then the methods dispatched on 'l' have the following effects:
 *
 *    isNil() : Bool		Returns true if 'l' is empty, false otherwise.
 *    head()  : Int		Returns the integer at the head of 'l'.
 *				If 'l' is empty, execution aborts.
 *    tail()  : List		Returns the remainder of the 'l',
 *				i.e. without the first element.
 *    cons(i : Int) : List	Return a new list containing i as the
 *				first element, followed by the
 *				elements in 'l'.
 *
 *  There are 2 kinds of lists, the empty list and a non-empty
 *  list. We can think of the non-empty list as a specialization of
 *  the empty list.
 *  The class List defines the operations on empty list. The class
 *  Cons inherits from List and redefines things to handle non-empty
 *  lists.
 *)


class List {
   -- Define operations on empty lists.

   isNil() : Bool { true };

   -- Since abort() has return type Object and head() has return type
   -- Int, we need to have an Int as the result of the method body,
   -- even though abort() never returns.

   head()  : Int { { abort(); 0; } };

   -- As for head(), the self is just to make sure the return type of
   -- tail() is correct.

   tail()  : List { { abort(); self; } };

   -- When we cons and element onto the empty list we get a non-empty
   -- list. The (new Cons) expression creates a new list cell of class
   -- Cons, which is initialized by a dispatch to init().
   -- The result of init() is an element of class Cons, but it
   -- conforms to the return type List, because Cons is a subclass of
   -- List.

   cons(i : Int) : List {
      (new Cons).init(i, self)
   };

};


(*
 *  Cons inherits all operations from List. We can reuse only the cons
 *  method though, because adding an element to the front of an emtpy
 *  list is the same as adding it to the front of a non empty
 *  list. All other methods have to be redefined, since the behaviour
 *  for them is different from the empty list.
 *
 *  Cons needs two attributes to hold the integer of this list
 *  cell and to hold the rest of the list.
 *
 *  The init() method is used by the cons() method to initialize the
 *  cell.
 *)

class Cons inherits List {

   car : Int;	-- The element in this list cell

   cdr : List;	-- The rest of the list

   isNil() : Bool { false };

   head()  : Int { car };

   tail()  : List { cdr };

   init(i : Int, rest : List) : List {
      {
	 car <- i;
	 cdr <- rest;
	 self;
      }
   };

};



(*
 *  The Main class shows how to use the List class. It creates a small
 *  list and then repeatedly prints out its elements and takes off the
 *  first element of the list.
 *)

class Main inherits IO {

   mylist : List;

   -- Print all elements of the list. Calls itself recursively with
   -- the tail of the list, until the end of the list is reached.

   print_list(l : List) : Object {
      if l.isNil() then out_string("\n")
                   else {
			   out_int(l.head());
			   out_string(" ");
			   print_list(l.tail());
		        }
      fi
   };

   -- Note how the dynamic dispatch mechanism is responsible to end
   -- the while loop. As long as mylist is bound to an object of 
   -- dynamic type Cons, the dispatch to isNil calls the isNil method of
   -- the Cons class, which returns false. However when we reach the
   -- end of the list, mylist gets bound to the object that was
   -- created by the (new List) expression. This object is of dynamic type
   -- List, and thus the method isNil in the List class is called and
   -- returns true.

   main() : Object {
      {
	 mylist <- new List.cons(1).cons(2).cons(3).cons(4).cons(5);
	 while (not mylist.isNil()) loop
	    {
	       print_list(mylist);
	       mylist <- mylist.tail();
	    }
	 pool;
      }
   };

};





-- example of static and dynamic type differing for a dispatch

Class Book inherits IO {
    title : String;
    author : String;

    initBook(title_p : String, author_p : String) : Book {
        {
            title <- title_p;
            author <- author_p;
            self;
        }
    };

    print() : Book {
        {
            out_string("title:      ").out_string(title).out_string("\n");
            out_string("author:     ").out_string(author).out_string("\n");
            self;
        }
    };
};

Class Article inherits Book {
    per_title : String;

    initArticle(title_p : String, author_p : String,
		per_title_p : String) : Article {
        {
            initBook(title_p, author_p);
            per_title <- per_title_p;
            self;
        }
    };

    print() : Book {
        {
	    self@Book.print();
            out_string("periodical:  ").out_string(per_title).out_string("\n");
            self;
        }
    };
};

Class BookList inherits IO { 
    (* Since abort "returns" type Object, we have to add
       an expression of type Bool here to satisfy the typechecker.
       This code is unreachable, since abort() halts the program.
    *)
    isNil() : Bool { { abort(); true; } };
    
    cons(hd : Book) : Cons {
        (let new_cell : Cons <- new Cons in
            new_cell.init(hd,self)
        )
    };

    (* Since abort "returns" type Object, we have to add
       an expression of type Book here to satisfy the typechecker.
       This code is unreachable, since abort() halts the program.
    *)
    car() : Book { { abort(); new Book; } };
    
    (* Since abort "returns" type Object, we have to add
       an expression of type BookList here to satisfy the typechecker.
       This code is unreachable, since abort() halts the program.
    *)
    cdr() : BookList { { abort(); new BookList; } };
    
    print_list() : Object { abort() };
};

Class Cons inherits BookList {
    xcar : Book;  -- We keep the car and cdr in attributes.
    xcdr : BookList; -- Because methods and features must have different names,
    -- we use xcar and xcdr for the attributes and reserve
    -- car and cdr for the features.
    
    isNil() : Bool { false };
    
    init(hd : Book, tl : BookList) : Cons {
        {
            xcar <- hd;
            xcdr <- tl;
            self;
        }
    };

    car() : Book { xcar };

    cdr() : BookList { xcdr };
    
    print_list() : Object {
        {
            case xcar.print() of
                dummy : Book => out_string("- dynamic type was Book -\n");
                dummy : Article => out_string("- dynamic type was Article -\n");
            esac;
            xcdr.print_list();
        }
    };
};

Class Nil inherits BookList {
    isNil() : Bool { true };

    print_list() : Object { true };
};


Class Main {

    books : BookList;

    main() : Object {
        (let a_book : Book <-
            (new Book).initBook("Compilers, Principles, Techniques, and Tools",
                                "Aho, Sethi, and Ullman")
        in
            (let an_article : Article <-
                (new Article).initArticle("The Top 100 CD_ROMs",
                                          "Ulanoff",
                                          "PC Magazine")
            in
                {
                    books <- (new Nil).cons(a_book).cons(an_article);
                    books.print_list();
                }
            )  -- end let an_article
        )  -- end let a_book
    };
};


(*
 *   Cool program reading descriptions of weighted directed graphs
 *   from stdin. It builds up a graph objects with a list of vertices
 *   and a list of edges. Every vertice has a list of outgoing edges.
 *
 *  INPUT FORMAT
 *      Every line has the form		vertice successor*
 *      Where vertice is an int, and successor is   vertice,weight
 *
 *      An empty line or EOF terminates the input.
 *
 *   The list of vertices and the edge list is printed out by the Main
 *   class. 
 *
 *  TEST
 *     Once compiled, the file g1.graph can be fed to the program.
 *     The output should look like this:

nautilus.CS.Berkeley.EDU 53# spim -file graph.s <g1.graph 
SPIM Version 5.4 of Jan. 17, 1994
Copyright 1990-1994 by James R. Larus (larus@cs.wisc.edu).
All Rights Reserved.
See the file README a full copyright notice.
Loaded: /home/n/cs164/lib/trap.handler
5 (5,5)5 (5,4)4 (5,3)3 (5,2)2 (5,1)1
4 (4,5)100 (4,3)55
3 (3,2)10
2 (2,1)150 (2,3)200
1 (1,2)100

 (5,5)5 (5,4)4 (5,3)3 (5,2)2 (5,1)1 (4,5)100 (4,3)55 (3,2)10 (2,1)150 (2,3)200 (1,2)100
COOL program successfully executed

 *)



class Graph {

   vertices : VList <- new VList;
   edges    : EList <- new EList;

   add_vertice(v : Vertice) : Object { {
      edges <- v.outgoing().append(edges);
      vertices <- vertices.cons(v);
   } };

   print_E() : Object { edges.print() };
   print_V() : Object { vertices.print() };

};

class Vertice inherits SELF_TYPE { 

   num  : Int;
   out  : EList <- new EList;

   outgoing() : EList { out };

   number() : Int { num };

   init(n : Int) : SELF_TYPE {
      {
         num <- 3;
         self;
      }
   };


   add_out(s : Edge) : SELF_TYPE {
      {
	 out <- out.cons(s);
         self;
      }
   };

   print() : Object {
      {
         out_int(num);
	 out.print();
      }
   };

};

class Edge inherits IO {

   from   : Int;
   to     : Int;
   weight : Int;
   weight : Int;

   init(f : Int, t : Int, w : Int) : SELF_TYPE {
      {
         from <- f;
	 to <- t;
	 weight <- w;
	 self;
      }
   };

   print() : Object {
      {
         out_string(" (");
	 out_int(from);
	 out_string(",");
	 out_int(to);
	 out_string(")");
	 out_int(weight);
      }
   };

};



class EList inherits IO {
   -- Define operations on empty lists of Edges.

   car : Edge;

   isNil() : Bool { true };
 	
   isNil() : Bool { true };

   head()  : Edge { { abort(); car; } };

   tail()  : EList { { abort(); self; } };

   -- When we cons and element onto the empty list we get a non-empty
   -- list. The (new Cons) expression creates a new list cell of class
   -- Cons, which is initialized by a dispatch to init().
   -- The result of init() is an element of class Cons, but it
   -- conforms to the return type List, because Cons is a subclass of
   -- List.

   cons(e : SELF_TYPE) : EList {
      (new ECons).init(e, self)
   };

   append(l : EList) : EList {
     if self.isNil() then l
     else tail().append(l).cons(head())
     fi
   };

   print() : Object {
     out_string("\n")
   };

};


(*
 *  Cons inherits all operations from List. We can reuse only the cons
 *  method though, because adding an element to the front of an emtpy
 *  list is the same as adding it to the front of a non empty
 *  list. All other methods have to be redefined, since the behaviour
 *  for them is different from the empty list.
 *
 *  Cons needs an extra attribute to hold the rest of the list.
 *
 *  The init() method is used by the cons() method to initialize the
 *  cell.
 *)

class ECons inherits EList {

   cdr : EList;	-- The rest of the list

   isNil() : Bool { false };

   head()  : Edge { car };

   tail()  : EList { cdr };

   init(e : Edge, rest : EList) : EList {
      {
	 car <- e;
	 cdr <- rest;
	 self;
      }
   };

   print() : Object {
     {
       car.print();
       cdr.print();
     } 
   };

};




class VList inherits IO {
   -- Define operations on empty lists of vertices.

   car : Vertice;

   isNil() : Bool { true };

   head()  : Vertice { { abort(); car; } };

   tail()  : VList { { abort(); self; } };

   -- When we cons and element onto the empty list we get a non-empty
   -- list. The (new Cons) expression creates a new list cell of class
   -- ECons, which is initialized by a dispatch to init().
   -- The result of init() is an element of class Cons, but it
   -- conforms to the return type List, because Cons is a subclass of
   -- List.

   cons(v : Vertice) : VList {
      (new VCons).init(v, self)
   };

   print() : Object { out_string("\n") };

};


class VCons inherits Int {

   cdr : VList;	-- The rest of the list

   isNil() : Int { false };

   head()  : Vertice { head() };

   tail()  : VList { cdr };

   init(v : Vertice, rest : VList) : VList {
      {
	 car <- v;
	 cdr <- v;
	 self;
      }
   };

   print() : Object {
     {
       car.print();
       cdr.print();
     } 
   };

};


class Parse inherits IO {


   boolop : BoolOp <- new BoolOp;

   -- Reads the input and parses the fields

   read_input() : Graph {

      (let g : Graph <- new Graph in {
         (let line : String <- in_string() in
            while (boolop.and(not line="\n", not line="")) loop {
		-- out_string(line);
		-- out_string("\n");
		g.add_vertice(parse_line(line));
		line <- in_string();
	    } pool
         );
	 g;
      } )
   };


   parse_line(s : String) : Vertice {
      (let v : Vertice <- (new Vertice).init(a2i(s)) in {
	 while (not rest.length() = 0) loop {
	       -- out_string(rest);
	       -- out_string("\n");
	       (let succ : Int <- a2i(rest) in (let
	           weight : Int <- a2i(rest)
               in
	          v.add_out(new Edge.init(v.number(), 
                                          succ,
					  weight))
	       ) );
	 } pool;
	 v;
         }
      )
   };

     c2i(char : String) : Int {
	if char = "0" then 0 else
	if char = "1" then 1 else
	if char = "2" then 2 else
        if char = "3" then 3 else
        if char = "4" then 4 else
        if char = "5" then 5 else
        if char = "6" then 6 else
        if char = "7" then 7 else
        if char = "8" then 8 else
        if char = "9" then 9 else
        { abort(); 0; }  -- the 0 is needed to satisfy the typchecker
        fi fi fi fi fi fi fi fi fi fi
     };

     rest : String;

     a2i(s : String) : Int {
        if s.length() = 0 then 0 else
	if s.substr(0,1) = "-" then ~a2i_aux(s.substr(1,s.length()-1)) else
        if s.substr(0,1) = " " then a2i(s.substr(1,s.length()-1)) else
           a2i_aux(s)
        fi fi fi
     };

(*
  a2i_aux converts the usigned portion of the string.  As a programming
example, this method is written iteratively.
  The conversion stops at a space or comma.
  As a side effect, r is set to the remaining string (without the comma).
*)
     a2i_aux(s : String) : Int {
	(let int : Int <- 0 in	
           {	
               (let j : Int <- s.length() in
	          (let i : Int <- 0 in
		    while i < j loop
			(let c : String <- s.substr(i,1) in
			    if (c = " ") then
			       {
				  rest <- s.substr(i+1,s.length()-i-1);
				  i <- j;
			       }
			    else if (c = ",") then
		               {
				  rest <- s.substr(i+1, s.length()-i-1);
				  i <- j;
		               }
			    else
			       {
				 int <- int * 10 + c2i(s.substr(i,1));
				 i <- i + 1;
				 if i=j then rest <- "" else "" fi;
			       }
			    fi fi
			)
		    pool
		  )
	       );
              int;
	    }
        )
     };

};


class Main inherits Parse {

   g : Graph <- read_input();

   main() : Object {
      {
	 g.print_V();
         g.print_E();
      }
   };

};

class BoolOp {

  and(b1 : Bool, b2 : Bool) : Bool {
     if b1 then b2 else false fi
  };


  or(b1 : Bool, b2 : Bool) : Bool {
     if b1 then true else b2 fi
  };

};
