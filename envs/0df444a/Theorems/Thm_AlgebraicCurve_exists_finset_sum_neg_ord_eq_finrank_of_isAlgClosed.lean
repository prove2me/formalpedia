-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
-- name    : AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/cf8ed5f7-65bd-5942-b45e-81bee149ff73
-- title:
--   Sum of pole orders of x equals [F:k(x)]
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field equipped with a $k$-algebra structure, let $x \in F$ be transcendental over $k$, and assume $F$ is finite-dimensional as a module over the intermediate field $k(x) =$ `IntermediateField.adjoin k {x}`. Here a place $P$ of $F$ over $k$ is a valuation subring of $F$ that contains the image of $k$ under the structure map, is not all of $F$, and is a principal ideal ring; for such a $P$ and $f \in F$, $\operatorname{ord}_P f$ is the integer $-\log$ of the value of $f$ under the $\mathbb{Z}^{m0}$-valued valuation attached to the height-one prime of $P$. The assertion is that there is a finite set $S$ of places of $F$ over $k$ whose members are exactly the places $P$ with $\operatorname{ord}_P x < 0$ — so in particular the set of poles of $x$ is finite — and such that $$\sum_{P \in S} \bigl(-\operatorname{ord}_P x\bigr) = [\,F : k(x)\,],$$ the right-hand side being the $k(x)$-dimension of $F$ viewed as an integer.
--
--   This is the classical statement that, over an algebraically closed constant field, the total pole order of a non-constant function $x$ on a curve equals the degree $[F:k(x)]$ of the associated covering of the projective line. It is the `Finset` form of the corresponding statement about the degree of the pole divisor, and is used in the project for counting places with prescribed behaviour, for instance in the computation of $\ell(0)$ and in the study of divisors built from floors of orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    ∃ S : Finset (Place k F), (∀ P, P ∈ S ↔ P.ord x < 0) ∧
      ∑ P ∈ S, (-P.ord x) = (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by sorry
