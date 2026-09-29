-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
-- name    : AlgebraicCurve.Place.ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/a3cc0f5a-ee93-5487-81f1-c26e1a71e350
-- title:
--   Order zero for elements integral over K[1/j]_{(1/j)} and inverse
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$: a valuation subring $\mathcal{O}_v =$ `v.toValuationSubring` of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Let $j \in F$ with $j \notin \mathcal{O}_v$, and let $P, Q \in F[X]$ be monic polynomials such that for every index $i$ the $i$-th coefficient of $P$, and likewise of $Q$, can be written as $p(j^{-1})/q(j^{-1})$ for some $p, q \in K[X]$ (evaluation via the $K$-algebra map into $F$) with the constant coefficient of $q$ nonzero. Suppose finally that $x \in F$ satisfies $P(x) = 0$ and $Q(x^{-1}) = 0$. Then $\operatorname{ord}_v(x) = 0$, where $\operatorname{ord}_v$ is the integer-valued invariant $-\log$ of the adic valuation attached to the height-one spectrum of $\mathcal{O}_v$.
--
--   This is the local statement that an element of $F$ which, together with its inverse, is integral over the local ring of the $j$-line at $j = \infty$ has order zero at every place where $j$ has a pole; the integrality is presented concretely through monic equations whose coefficients are ratios of polynomials in $j^{-1}$ with invertible denominator. It is used by [`ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto`](thm.html#ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem AlgebraicCurve.Place.ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {j : F} (hj : j ∉ v.toValuationSubring)
    {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ P.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    (hQc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ Q.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    {x : F} (hx : P.eval x = 0) (hx' : Q.eval x⁻¹ = 0) :
    v.ord x = 0 := by sorry
