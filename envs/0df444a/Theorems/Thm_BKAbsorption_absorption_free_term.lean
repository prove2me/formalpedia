-- Prove2me | Theorems.Thm_BKAbsorption_absorption_free_term
-- name    : BKAbsorption.absorption_free_term
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T14:12:34.992537+00:00
-- url     : https://prove2.me/theorems/08018434-7d73-4b85-bae5-ad577694e2c0
-- title:
--   A term reaching every element from every coordinate
-- statement:
--   $L$ is a signature without relation symbols. A finite algebra $A$ lies in a Taylor variety: it is idempotent ($f(a,\dots,a)=a$ for every basic operation) and satisfies the identities of a fixed Taylor term $t$ of arity $k$: for each $j<k$, $t(\square_0,\dots,\square_{k-1})\approx t(\triangle_0,\dots,\triangle_{k-1})$ with $\square_i,\triangle_i\in\{x,y\}$, $\square_j=x$, $\triangle_j=y$. $B\trianglelefteq A$ ($B$ absorbs $A$): $B$ is a subuniverse and some term operation $t$ gives $t(a_0,\dots,a_{n-1})\in B$ whenever all $a_i$ but at most one lie in $B$; proper means $\emptyset\neq B\neq A$; $B\trianglelefteq\!\!\trianglelefteq A$: $B$ is nonempty, absorbs $A$, and no proper subalgebra of $B$ absorbs $A$. If $A$ has no proper absorbing subuniverse, then there is a term operation $v$ of positive arity $n$ such that for all $b,c\in A$ and every $i<n$ there are $a_0,\dots,a_{n-1}\in A$ with $a_i=b$ and $v(a_0,\dots,a_{n-1})=c$.
-- source:
--   L. Barto, M. Kozik, Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem, Logical Methods in Computer Science 8(1:07) 2012, https://doi.org/10.2168/LMCS-8(1:7)2012 (arXiv:1201.0557), Prop 2.7

import Definitions.Def_BKAbsorption_defs

universe u v w w'

open FirstOrder FirstOrder.Language

namespace BKAbsorption

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Barto–Kozik, Proposition 2.7.  Let `A` be a finite algebra in a Taylor variety (here: `A`
satisfies the idempotency and Taylor identities of a Taylor datum `T`) and suppose that `A` has
no proper absorbing subalgebra.  Then there is a term operation `v ∈ Clo(A)` (of positive arity
`n`) such that for all `b, c ∈ A` and every coordinate `i < n` there are `a₀, …, a_{n-1} ∈ A`
with `aᵢ = b` and `v(a₀, …, a_{n-1}) = c`. -/
theorem absorption_free_term {A : Type w} [L.Structure A] [Finite A] (T : TaylorDatum L)
    (hA : IsTaylorAlg T A) (hnp : ¬ HasProperAbsorbing L A) :
    ∃ (n : ℕ) (v : L.Term (Fin n)), 0 < n ∧
      ∀ (b c : A) (i : Fin n), ∃ a : Fin n → A, a i = b ∧ v.realize a = c := by sorry

end BKAbsorption
