-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
-- name    : AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/f5bb46d2-4a6d-59d3-a6b3-9b660446d26c
-- title:
--   Divisors of rational functions on P¹ have degree zero
-- statement:
--   Let $K$ be a field and let $f$ be an element of the rational function field $\mathrm{RatFunc}\,K$. Here a place of $\mathrm{RatFunc}\,K$ over $K$ is a valuation subring of $\mathrm{RatFunc}\,K$ that contains the image of $K$, is not the whole field, and is a principal ideal ring; for such a place $v$ and an element $g$, $v.\mathrm{ord}\,g$ is the integer $-\log$ of the value of $g$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to $v$, i.e. the order of vanishing of $g$ at $v$. A divisor is a finitely supported function $D$ from the set of such places to $\mathbb{Z}$, and its degree is the finite sum $\sum_v D(v)\cdot \deg v$, where $\deg v$ is the degree attached to the place $v$. The assertion is: if $D$ is a divisor such that $D(v) = v.\mathrm{ord}\,f$ for every place $v$ of $\mathrm{RatFunc}\,K$ over $K$, then $\mathrm{Divisor.degree}\,D = 0$. No nonvanishing hypothesis on $f$ is imposed; for $f = 0$ the hypothesis forces $D = 0$.
--
--   This is the degree-zero property of principal divisors (the sum, or product, formula) for the rational function field $K(t)$, that is, for $\mathbb{P}^1_K$. It underlies the computation of the divisor class group of the rational function field and is used, among other things, to show that places of $K(t)$ have degree one when $K$ is algebraically closed and to evaluate divisors at the place at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord {K : Type*} [Field K] {f : RatFunc K} (D : Divisor K (RatFunc K)) (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) : Divisor.degree D = 0 := by sorry
