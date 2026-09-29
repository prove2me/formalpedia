-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
-- name    : AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/8d31be42-bebd-5aa9-b199-3a9cf9ed31f0
-- title:
--   Zero sum of x-a equals [F:k(x)] over ̄ k
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field equipped with a $k$-algebra structure. Let $x \in F$ be transcendental over $k$, assume $F$ is finite-dimensional as a module over the intermediate field $k(x) =$ `IntermediateField.adjoin k {x}`, and let $a \in k$. Here a place of $F$ over $k$ (the structure `Place k F`) is a valuation subring of $F$ containing $\operatorname{algebraMap} k F(b)$ for every $b \in k$, different from all of $F$, and whose underlying ring is a principal ideal ring; for such a place $P$ and $f \in F$, $P.\mathrm{ord}(f)$ is the integer $-\log$ of the value of $f$ under the valuation of $F$ attached to the height-one prime of $P$. The assertion is that there exists a finite set $S$ of places of $F$ over $k$ such that a place $P$ lies in $S$ precisely when $P.\mathrm{ord}(x - \operatorname{algebraMap} k F(a)) > 0$, and such that $$\sum_{P \in S} P.\mathrm{ord}\bigl(x - \operatorname{algebraMap} k F(a)\bigr) = \bigl[F : k(x)\bigr],$$ the right-hand side being $\operatorname{finrank}_{k(x)} F$ regarded as an integer. In particular the set of places at which $x - a$ has a zero is finite, and the zeros of $x-a$ counted with multiplicity total $[F:k(x)]$.
--
--   This is the classical statement that, over an algebraically closed constant field, the fibre of the map $x$ above a point $a \in k$ has total multiplicity equal to the degree $[F:k(x)]$ (Stichtenoth, Theorem 1.4.11), packaged as an explicit finite sum rather than as an equality of divisor degrees. It is used for the ramification estimates for the covering $X_1(M) \to \mathbb{P}^1_j$ and for counting zeros against supersingular points; among its consumers are [`AlgebraicCurve.finrank_adjoin_le_mul_natCard_place_ord_sub_algebraMap_pos_of_forall_ord_le`](thm.html#AlgebraicCurve.finrank_adjoin_le_mul_natCard_place_ord_sub_algebraMap_pos_of_forall_ord_le) and lemmas on cuspidal and non-cuspidal specialisations of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) (a : k) :
    ∃ S : Finset (Place k F), (∀ P, P ∈ S ↔ 0 < P.ord (x - algebraMap k F a)) ∧
      ∑ P ∈ S, P.ord (x - algebraMap k F a) = (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by sorry
