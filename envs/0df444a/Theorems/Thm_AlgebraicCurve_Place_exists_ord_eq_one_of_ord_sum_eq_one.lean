-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one
-- name    : AlgebraicCurve.Place.exists_ord_eq_one_of_ord_sum_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/1cc11c8a-fabf-57b3-a783-a70108ec7f7c
-- title:
--   Order-one combinations have an order-one summand
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ which contains $\operatorname{algebraMap}_{K,F}(a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring; write $\operatorname{ord}_v(g) = -\log\bigl(v_{\mathrm{adic}}(g)\bigr)$ for the integer attached to $g \in F$ by the $\mathbb{Z}^{m0}$-valued valuation of the associated height-one prime (so $\operatorname{ord}_v(0) = 0$). Let $\iota$ be a type, $s$ a finite subset of $\iota$, and let $c : \iota \to K$ and $f : \iota \to F$ be families. Assume that for every $i \in s$ either $f_i = 0$ or $\operatorname{ord}_v(f_i) \ge 1$, and that
--   $$\operatorname{ord}_v\Bigl(\sum_{i \in s} \operatorname{algebraMap}_{K,F}(c_i)\, f_i\Bigr) = 1 .$$
--   Then there is an $i \in s$ with $\operatorname{ord}_v(f_i) = 1$. Note that the hypothesis and conclusion use the convention $\operatorname{ord}_v(0) = 0$, so a vanishing summand automatically fails to have order $1$.
--
--   This is the elementary ultrametric fact that a $K$-linear combination of functions vanishing at a place $v$ can have order exactly $1$ at $v$ only if one of the functions is itself a uniformiser at $v$. It is used in the construction of local charts on the modular curve, in [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot), to transfer the property of being a local parameter from one family of functions to another.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Place.exists_ord_eq_one_of_ord_sum_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → F)
    (hf : ∀ i ∈ s, f i = 0 ∨ 1 ≤ v.ord (f i))
    (h : v.ord (∑ i ∈ s, algebraMap K F (c i) * f i) = 1) :
    ∃ i ∈ s, v.ord (f i) = 1 := by sorry
