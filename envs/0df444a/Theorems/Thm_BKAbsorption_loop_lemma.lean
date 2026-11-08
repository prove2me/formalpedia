-- Prove2me | Theorems.Thm_BKAbsorption_loop_lemma
-- name    : BKAbsorption.loop_lemma
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T14:13:15.345094+00:00
-- url     : https://prove2.me/theorems/6eb0e885-dc70-45c9-a0de-325e008d46a0
-- title:
--   Loop Lemma
-- statement:
--   $L$ is a signature without relation symbols. A finite algebra $A$ lies in a Taylor variety: it is idempotent ($f(a,\dots,a)=a$ for every basic operation) and satisfies the identities of a fixed Taylor term $t$ of arity $k$: for each $j<k$, $t(\square_0,\dots,\square_{k-1})\approx t(\triangle_0,\dots,\triangle_{k-1})$ with $\square_i,\triangle_i\in\{x,y\}$, $\square_j=x$, $\triangle_j=y$. $B\trianglelefteq A$ ($B$ absorbs $A$): $B$ is a subuniverse and some term operation $t$ gives $t(a_0,\dots,a_{n-1})\in B$ whenever all $a_i$ but at most one lie in $B$; proper means $\emptyset\neq B\neq A$; $B\trianglelefteq\!\!\trianglelefteq A$: $B$ is nonempty, absorbs $A$, and no proper subalgebra of $B$ absorbs $A$. Let $E$ be a subuniverse of $A^2$ such that the digraph $(A,E)$ is smooth (every vertex has an incoming and an outgoing edge) and has algebraic length $1$ (some vertex $a$ is joined to itself by an oriented path with one more forward than backward edge). Then $(a,a)\in E$ for some $a$. Moreover, if a nonempty absorbing subuniverse $I$ of $A$ lies in a weak component of algebraic length $1$, then there are $J\trianglelefteq\!\!\trianglelefteq A$ and $a\in J$ with $(a,a)\in E$.
-- source:
--   L. Barto, M. Kozik, Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem, Logical Methods in Computer Science 8(1:07) 2012, https://doi.org/10.2168/LMCS-8(1:7)2012 (arXiv:1201.0557), Thm 3.6

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Theorem 3.6 (Loop Lemma).  Let `A` be a finite algebra in a Taylor variety and
let `G = (A, E)` be a smooth digraph of algebraic length `1` such that `E` is a subuniverse of
`A²`.  Then `G` contains a loop.  Moreover, if there is a (nonempty) absorbing subuniverse `I`
of `A` contained in a weak component of `G` of algebraic length `1`, then the loop can be found
in some `J` with `J ⊴⊴ A`. -/
theorem loop_lemma {A : Type w} [L.Structure A] [Finite A] (T : TaylorDatum L)
    (hA : IsTaylorAlg T A) (E : L.Substructure (A × A)) (hsm : Smooth (E : Set (A × A)))
    (hlen : ∃ a, Walk (E : Set (A × A)) a a 1) :
    (∃ a, (a, a) ∈ E) ∧
    (∀ I : Set A, IsAbsorbing L I → I.Nonempty →
      (∃ a, Walk (E : Set (A × A)) a a 1 ∧ ∀ x ∈ I, ∃ z, Walk (E : Set (A × A)) a x z) →
      ∃ J : Set A, MinAbsorbing L J ∧ ∃ a ∈ J, (a, a) ∈ E) := by sorry

end BKAbsorption
