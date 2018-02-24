package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._

  /*
  * CSCI 3155: Lab 3
  * Lucas Schaack
  *
  * Partner: <Your Partner's Name>
  * Collaborators: <Any Collaborators>
  */

  /*
  * Fill in the appropriate portions above by replacing things delimited
  * by '<'... '>'.
  *
  * Replace the '???' expression with your code in each function.
  *
  * Do not make other modifications to this template, such as
  * - adding "extends App" or "extends Application" to your Lab object,
  * - adding a "main" method, and
  * - leaving any failing asserts.
  *
  * Your lab will not be graded if it does not compile.
  *
  * This template compiles without error. Before you submit comment out any
  * code that does not compile or causes a failing assert. Simply put in a
  * '???' as needed to get something that compiles without error. The '???'
  * is a Scala expression that throws the exception scala.NotImplementedError.
  */

  /*
  * The implementations of these helper functions for conversions can come
  * Lab 2. The definitions for the new value type for Function are given.
  */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => {
        try {
          s.toDouble // if the string consists only of a double
        } catch {
          case nfe: NumberFormatException => Double.NaN // all other cases
        }
      }
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => { n != 0 }
      case S(s) => { !s.isEmpty() }
      case Function(_, _, _) => true
      case Undefined => false
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case N(n) => n.toString
      case B(b) => if (b) "true" else "false"
      // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
      // of the function (from the input program).
      case Function(_, _, _) => "function"
      case Undefined => "undefined" // delete this line when done
    }
  }

  /*
  * Helper function that implements the semantics of inequality
  * operators Lt, Le, Gt, and Ge on values.
  *
  * We suggest a refactoring of code from Lab 2 to be able to
  * use this helper function in eval and step.
  */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)

    (v1, v2) match {
      case (S(s1), S(s2)) => (bop: @unchecked) match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case _ => {
        val (n1, n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
      }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
  * Start by copying your code from Lab 2 here.
  */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => lookup(env, x)

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      // ****** Your cases here
      case Unary(uop, e1) => {
        uop match {
          case Neg => N(-toNumber(eval(env, e1)))
          case Not => B(!toBoolean(eval(env, e1)))
        }
      }

      case Binary(bop, e1, e2) => {
        bop match {
          case Plus => {
            (bop, e1, e2) match {
              // if either e1: S(s) or e2: S(s), should concatenate
              case (_, S(_), _) | (_, _, S(_)) => {
                S(toStr(eval(env, e1)) + toStr(eval(env, e2)))
              }
              // otherwise just add as numbers
              case _ => {
                N(toNumber(eval(env, e1)) + toNumber(eval(env, e2)))
              }
            }
          }
          // begin easy mode
          case Minus => { // much easier than Plus--no concatenation required.
            N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
          }
          case Times => {
            N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
          }
          case Div => {
            N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))
          }

          case Eq => {
            val v1 = eval(env, e1)
            val v2 = eval(env, e2)

            (v1, v2) match {
              case ((Function(_, _, _),_) | (_, Function(_, _, _))) => throw DynamicTypeError(e)
              case _ => B(v1 == v2)
            }
          }

          case Ne => {
            val v1 = eval(env, e1)
            val v2 = eval(env, e2)

            (v1, v2) match {
              case ((Function(_, _, _),_) | (_, Function(_, _, _))) => throw DynamicTypeError(e)
              case _ => B(v1 == v2)
            }
          }

          case Lt => {
            B(inequalityVal(Lt, eval(env, e1), eval(env, e2)))
            // B(toNumber(eval(env, e1)) < toNumber(eval(env, e2)))
          }
          case Le => {
            B(inequalityVal(Le, eval(env, e1), eval(env, e2)))
            // B(toNumber(eval(env, e1)) <= toNumber(eval(env, e2)))
          }
          case Gt => {
            B(inequalityVal(Gt, eval(env, e1), eval(env, e2)))
            // B(toNumber(eval(env, e1)) > toNumber(eval(env, e2)))
          }
          case Ge => {
            B(inequalityVal(Ge, eval(env, e1), eval(env, e2)))
            // B(toNumber(eval(env, e1)) >= toNumber(eval(env, e2)))
          }
          // end easy mode
          case And => {
            // weird short circuit behavior...return second arg if first is t
            val v1 = eval(env, e1)
            if (toBoolean(v1)) eval(env, e2) else v1
          }
          // returns first truthy value or last falsey value
          case Or => {
            val v1 = eval(env, e1)
            if (toBoolean(v1)==true) v1 else eval(env, e2)
          }
          case Seq => {
            eval(env, e1)
            eval(env, e2)
          }
          case _ => Undefined
        }
      }

      case ConstDecl(x:String, e1:Expr, e2:Expr) => {

        val v:Expr = eval(env,e1)
        eval(extend(env,x,v),e2)
      }

      case If(e1, e2, e3) => {
        if (toBoolean(eval(env, e1))) {
          eval(env, e2)
        } else {
          eval(env, e3)
        }
      }

      case Call(e1, e2) => {
        val v1 = eval(env, e1)
        v1 match {
          case Function(None, x, e) => {
            val v2 = eval(env, e2)
            eval(extend(env,x,v2),e)
          }
          case Function(Some(x1), x2, e) =>{
            val v2 = eval(env, e2)
            eval(extend(extend(env, x1, v1), x2, v2), e)
          }
          case _ => throw new DynamicTypeError(e)
        }
      }
      case _ => throw new UnsupportedOperationException

    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(ex) => loop(ex, n + 1)
    }
    loop(e0, 0)
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      /* Base Cases */
      case N(_) | B(_) | Undefined | S(_) => e
      // The base functionality of this method
      case Var(y) => {
        if (y == x) {
          v // v is an expr of the subset value matching name x
        } else {
          Var(y)
        }
      }

      /* Inductive cases? */
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, substitute(e1,v,x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1,v,x), substitute(e2,v,x))
      case If(e1, e2, e3) => If(substitute(e1,v,x), substitute(e2,v,x), substitute(e3,v,x))
      case Call(e1, e2) => Call(substitute(e1,v,x), substitute(e2,v,x))

      case Function(None, y, e1) => {
        if (y == x) {
          Function(None, y, e1)
        } else {
          Function(None, y, substitute(e1,v,x))
        }
      }

      case Function(Some(y1), y2, e1) => {
        if (y2 == x || y1 == x) {
          Function(Some(y1), y2, e1)
        } else {
          Function(Some(y1),y2,substitute(e1,v,x))
        }
      }

      case ConstDecl(y, e1, e2) => {
        if (y == x) {
          ConstDecl(y,substitute(e1,v,x),e2)
        } else {
          ConstDecl(y,substitute(e1,v,x), substitute(e2,v,x))
        }
      }
    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      // ****** Your cases here
      case Unary(Neg, v) if isValue(v) => N(-toNumber(v))
      case Unary(Not, v) if isValue(v) => B(!toBoolean(v))

      case Binary(Seq, v1, v2) if isValue(v1) => v2

      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (_,S(_)) => S(toStr(v1) + v2)
        case (S(_),_) => S(v1 + toStr(v2))
        case (_,_) => N(toNumber(v1) + toNumber(v2))
      }

      case Binary(Minus, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) - toNumber(v2))
      case Binary(Times, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) * toNumber(v2))
      case Binary(Div, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) / toNumber(v2))

      case Binary(Lt, v1, v2) if (isValue(v1) && isValue(v2)) => {
        B(inequalityVal(Lt, v1, v2))
      }

      case Binary(Le, v1, v2) if (isValue(v1) && isValue(v2)) => {
        B(inequalityVal(Le, v1, v2))
      }

      case Binary(Gt, v1, v2) if (isValue(v1) && isValue(v2)) => {
        B(inequalityVal(Gt, v1, v2))
      }

      case Binary(Ge, v1, v2) if (isValue(v1) && isValue(v2)) => {
        B(inequalityVal(Ge, v1, v2))
      }

      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (Function(_,_,_), _) => throw DynamicTypeError(e)
        case (_, Function(_,_,_)) => throw DynamicTypeError(e)
        case (_, _) => B(v1 != v2)
      }

      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (Function(_,_,_), _) => throw DynamicTypeError(e)
        case (_, Function(_,_,_)) => throw DynamicTypeError(e)
        case (_, _) => B(v1 == v2)
      }

      case Binary(And, v1, v2) if isValue(v1) && isValue(v2) => {
        if (toBoolean(v1) == true) {
          v2
        } else if (toBoolean(v1) == false) {
          v1
        } else { // if (toBoolean(v2) == false) {
          v2
        }
      }

      case Binary(Or, v1, v2) if isValue(v1) && isValue(v2) => {
        if (toBoolean(v1) == true) {
          v1
        } else {
          v2
        }
      }

      case If(v1, v2, v3) if isValue(v1) => {
        if (toBoolean(v1)) { // v1 ? ...
          v2 // ... v2 : ...
        } else {
          v3 // ... v3;
        }
      }

      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)

      case Call(v1,v2) if isValue(v1) && isValue(v2) => v1 match {
        case Function(None,x,body) => substitute(body,v2,x)
        case Function(Some(s),x,body) => substitute(substitute(body,v1,s),v2,x)
        case _ => throw DynamicTypeError(e)
      }

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

      // ****** Your cases here
      case Unary(uop, e1) if !isValue(e1) => Unary(uop, step(e1))

      case Binary(bop, e1, e2) if !isValue(e1) => Binary(bop, step(e1), e2) //do i need the if isvalue case

      case Binary(bop, e1, e2) if isValue(e1) => (bop, e1, e2) match {
        case (Eq, Function(_, _, _), e2) => throw DynamicTypeError(e)
        case (Eq, e1, Function(_, _, _)) => throw DynamicTypeError(e)
        case (Ne, Function(_, _, _), e2) => throw DynamicTypeError(e)
        case (Ne, e1, Function(_, _, _)) => throw DynamicTypeError(e)
        case (_, _, _) => Binary(bop,e1, step(e2))
      }

      case If(e1, e2, e3) if !isValue(e1) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) if !isValue(e1) => ConstDecl(x, step(e1), e2)

      case Call(v1, e2) if (isValue(v1)) => v1 match {
        case Function(_, _, _) => Call(v1, step(e2))
        case _ => throw DynamicTypeError(e)
      }

      case Call(e1, e2) => Call(step(e1), e2)

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => {
        throw new AssertionError("Gremlins: internal error, step should not be called on values.")
      }
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}