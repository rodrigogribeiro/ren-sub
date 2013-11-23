\documentclass{article}
\usepackage{a4}
\usepackage{palatino}
\usepackage{natbib}
\usepackage{amsfonts}
\usepackage{stmaryrd}
\usepackage{upgreek}
\usepackage{url}


\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff


\newcommand{\M}[1]{\mathsf{#1}}
\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}
\newcommand{\T}[1]{\raisebox{0.02in}{\tiny\green{\textsc{#1}}}}

\newcommand{\us}[1]{\_\!#1\!\_}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"

%format -> = "\blue{\rightarrow}"

\newcommand{\nudge}[1]{\marginpar{\footnotesize #1}}

%format rewrite = "\mathkw{rewrite}"
%format constructor = "\mathkw{constructor}"
%format Set = "\D{Set}"
%format Ty = "\D{Ty}"
%format iota = "\C{\upiota}"
%format ->> = "\C{\rhd}"
%format _->>_ = "\_\!" ->> "\!\_"
%format Cx = "\D{Cx}"
%format Em = "\C{\mathcal{E}}"
%format <: = "\D{\in}"
%format _<:_ = "\us{" <: "}"
%format Gam = "\V{\Gamma}"
%format Ren = "\F{Ren}"
%format Sub = "\F{Sub}"
%format Del = "\V{\Delta}"
%format sg = "\V{\sigma}"
%format tau = "\V{\tau}"
%format var = "\C{var}"
%format lam = "\C{lam}"
%format app = "\C{app}"
%format :: = "\!\raisebox{ -0.09in}[0in][0in]{\red{\textsf{`}}\,}"
%format _::_ = _ :: _
%format ? = "\orange{?}"


\parskip 0.1in
\parindent 0in

\begin{document}
   \title{Type safe renaming and substitution for simple typed $\lambda$-calculus}

   \author{Rodrigo Ribeiro}

   \maketitle

I resolved to implement this in Agda as a way to:
\begin{itemize}
  \item Learn how to use lhs2TeX with literate Agda code a la McBride.
  \item Study this draft of McBride in order to develop things in Agda latter!
\end{itemize}

The first point here is the definition of types. We will consider types just
formed by some base type and arrow's:

%if False
\begin{code}
module RenSub where

data List (X : Set) : Set where
  <>  : List X
  _,_ : X -> List X -> List X

infixr 4 _,_

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
\end{code}
%endif
   
\begin{code}
data Ty : Set where
  iota  : Ty
  _->>_ : Ty -> Ty -> Ty

infixr 5 _->>_
\end{code}

Next, we need contexts to hold type information for terms in DeBruijn notation.
Contexts are just snoc-lists of types.

\begin{code}
data Cx : Set where
  Em   : Cx
  _::_ : Cx -> Ty -> Cx

infixl 4 _::_
\end{code}

Now, DeBruijn indexes are just context membership evidence!

\begin{code}
data _<:_ (tau : Ty) : Cx -> Set where
  here  : forall {Gam}                  -> tau <: Gam :: tau
  there : forall {Gam sg} -> tau <: Gam -> tau <: Gam :: sg

infix 3 _<:_
\end{code}

That done, we can build well typed terms by writing syntax-directed
rules for the typing judgment.

%format !- = "\D{\vdash}"
%format _!-_ = "\us{" !- "}"
\newcommand{\negs}{\hspace*{ -0.3in}}
\begin{code}
data _!-_ (Gam : Cx) : Ty -> Set where

  var :  forall {tau}
         ->  tau <: Gam
         --  \negs -------------
         ->  Gam !- tau

  lam :  forall {sg tau}
         ->  Gam :: sg !- tau
         --  \negs ------------------
         ->  Gam !- sg ->> tau

  app :  forall {sg tau}
         ->  Gam !- sg ->> tau  ->  Gam !- sg
         --  \negs -------------------------------
         ->  Gam !- tau

infix 3 _!-_
\end{code}

Now, I can start the real business here: definition of substitution and renaming operations.

\begin{code}
Ren : Cx -> Cx -> Set
Ren Gam Del  = forall {tau} -> tau <: Gam -> tau <: Del

Sub : Cx -> Cx -> Set
Sub Gam Del  = forall {tau} -> tau <: Gam -> Del !- tau
\end{code}

The main issue when using DeBruijn indexes is the problematic (and boring...) index shift when
context grows at each abstraction.

\begin{code}
_<><_ : Cx -> List Ty -> Cx 
xz <>< <>        = xz
xz <>< (x , xs)  = xz :: x <>< xs

infixl 4 _<><_
\end{code}

%format Xi = "\V{\Xi}"
%format // = "\F{/\!\!/}"
%format _//_ = "\us{" // "}"
%format theta = "\V{\theta}"
%format Shub = "\F{Shub}"
We may then define the \emph{shiftable} simultaneous substitutions
from |Gam| to |Del|
as type-preserving mappings from the variables in any extension of |Gam| to
terms in the same extension of |Del|.
\begin{code}
Shub : Cx -> Cx -> Set
Shub Gam Del = forall Xi -> Sub (Gam <>< Xi) (Del <>< Xi)
\end{code}

By the computational behaviour of |<><|, a |Shub Gam Del| can be used
as a |Shub (Gam :: sg) (Del :: sg)|, so we can push substitutions under
binders very easily.
\begin{code}
_//_ : forall {Gam Del}(theta : Shub Gam Del){tau} -> Gam !- tau -> Del !- tau
theta // var i       = theta <> i
theta // lam {sg} t  = lam ((λ Xi → theta (sg , Xi)) // t)
theta // app f s     = app (theta // f) (theta // s)
\end{code}

Of course, we shall need to construct some of these joyous shubstitutions.
Let us first show that any simultaneous renaming can be made shiftable by
iterative weakening.
%format wkr = "\F{wkr}"
%format ren = "\F{ren}"

\begin{code}
wkr :  forall {Gam Del sg} -> Ren Gam Del -> Ren (Gam :: sg) (Del :: sg)
wkr r here     = here
wkr r (there i)  = there (r i)

ren :  forall {Gam Del} -> Ren Gam Del -> Shub Gam Del
ren r <>         = λ {tau} z → var (r z)
ren r (_ , Xi)   = ren (wkr r) Xi
\end{code}

%format wks = "\F{wks}"
%format sub = "\F{sub}"
With renaming available, we can play the same game for substitutions.
\begin{code}
wks :  forall {Gam Del sg} -> Sub Gam Del -> Sub (Gam :: sg) (Del :: sg)
wks s here     = var here
wks s (there i)  = ren there // s i

sub :  forall {Gam Del} -> Sub Gam Del -> Shub Gam Del
sub s <>         = s
sub s (_ , Xi)   = sub (wks s) Xi
\end{code}


\end{document}
