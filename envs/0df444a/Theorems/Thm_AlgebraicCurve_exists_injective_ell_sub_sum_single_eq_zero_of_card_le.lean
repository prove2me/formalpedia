-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_injective_ell_sub_sum_single_eq_zero_of_card_le
-- name    : AlgebraicCurve.exists_injective_ell_sub_sum_single_eq_zero_of_card_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/ad8ebd2b-3ada-516c-98a4-a2b2c752c868
-- title:
--   Degree-one places killing a Riemann–Roch space, avoiding a finite set
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`, i.e. every nonzero $f \in F$ has a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$, every residue field $\kappa(v)$ is finite-dimensional over $K$, and $\Omega_{F/K}$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ and a principal ideal ring, $\deg v = \dim_K \kappa(v)$, and a divisor is a finitely supported function from places to $\mathbb{Z}$, of degree $\sum_v D(v)\deg v$. Assume moreover $F$ is essentially of finite type over $K$. Let $G$ be a divisor, $n$ a natural number with $\ell(G) = n$, where $\ell(D) = \dim_K L(D)$ is the $K$-dimension of the Riemann–Roch space of $D$, and let $X, S$ be finite sets of places such that every $v \in S$ has $\deg v = 1$ and $\#X + \deg G + 1 \le \#S$ as integers. Then there is an injective family $Q : \mathrm{Fin}\,n \to$ places with every $Q_l \in S \setminus X$ and $\ell\bigl(G - \sum_{l} Q_l\bigr) = 0$, the sum being the divisor $\sum_l \mathrm{single}(Q_l, 1)$.
--
--   This is the standard greedy construction placing $n = \ell(G)$ rational points in general position with respect to $G$, drawn from a prescribed pool $S$ of degree-one places and avoiding a prescribed finite set $X$. It is used in the construction of functions and sections on modular curves, where it feeds [`ModularCurve.exists_injective_riemannRochSpace_canonicalDivisorOf_sub_eq_bot`](thm.html#ModularCurve.exists_injective_riemannRochSpace_canonicalDivisorOf_sub_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_injective_ell_sub_sum_single_eq_zero_of_card_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_injective_ell_sub_sum_single_eq_zero_of_card_le
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (G : Divisor K F) {n : ℕ} (hn : ell G = n)
    (X S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1)
    (hcard : (X.card : ℤ) + Divisor.degree G + 1 ≤ S.card) :
    ∃ Q : Fin n → Place K F, Function.Injective Q ∧ (∀ l, Q l ∈ S ∧ Q l ∉ X) ∧
      ell (G - ∑ l, Finsupp.single (Q l) 1) = 0 := by sorry
