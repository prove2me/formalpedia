-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_zsmul_mk
-- name    : AlgebraicCurve.Pic0.zsmul_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/233f8b8e-9734-5a46-b2fc-b00da497bc2c
-- title:
--   Integer multiples commute with passage to divisor classes
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $m$ be an integer, and let $D$ be an element of `Divisor.degZero`, that is, a divisor of degree zero. Here a place of $F$ over $K$ is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function from the set of such places to $\mathbb{Z}$; the degree homomorphism sends a divisor to the sum of its coefficients weighted by the integer invariant `deg` of the corresponding place, and `Divisor.degZero` is its kernel. The group `Pic0` is the quotient of `Divisor.degZero` by the subgroup of those degree-zero divisors that are principal, i.e. that satisfy the predicate `IsPrincipal`: there is a nonzero $f \in F$ whose order at every place gives the coefficient of the divisor there, and `Pic0.mk` is the associated quotient map. The assertion is that $m \cdot \mathrm{mk}(D) = \mathrm{mk}(m \cdot D)$, the scalar multiplication on the left being that of the additive group `Pic0` and on the right that of `Divisor.degZero`.
--
--   This is the routine compatibility of the divisor-class map with integer multiples, used whenever orders of divisor classes are computed from explicit multiples of a degree-zero divisor. It is cited in the proof that a class is trivial as soon as the corresponding multiple of the divisor is principal, and in the determination of the order of the cuspidal class on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_zsmul_mk.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.zsmul_mk {K F : Type*} [Field K] [Field F] [Algebra K F] (m : ℤ) (D : Divisor.degZero (K := K) (F := F)) : m • Pic0.mk D = Pic0.mk (m • D) := by sorry
