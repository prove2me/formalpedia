-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap
-- name    : AlgebraicCurve.exists_divisor_eq_max_ord_sub_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/bfacb035-0084-5562-9e11-8a52d16fde3c
-- title:
--   Existence of the divisor of zeros of x-a
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume `HasPrincipalDivisors K F`, i.e. that for every nonzero $f \in F$ there is a finitely supported integer-valued function $D$ on the places of $F/K$ with $D(v) = \operatorname{ord}_v(f)$ for every place $v$ and with $\deg D = 0$; here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring, $\operatorname{ord}_v(f)$ is minus the logarithm of the value of $f$ under the adic valuation attached to the height-one prime of $v$, and the degree is the sum of the coefficients weighted by the residue degrees of the places. Let $x \in F$ be transcendental over $K$ and let $a \in K$. Then there exists a divisor $D$ on the places of $F/K$, that is a finitely supported function from `Place K F` to $\mathbb{Z}$, such that for every place $v$ one has $D(v) = \max\bigl(0, \operatorname{ord}_v(x - \operatorname{algebraMap}_{K,F}(a))\bigr)$. No assertion is made about the degree of $D$.
--
--   This is the existence of the divisor of zeros of $x-a$, the positive part of the principal divisor $\operatorname{div}(x-a)$; its support enumerates the places of $F/K$ lying over the value $a$ of $x$, so that the fibre of $x$ above $a$ is finite. It feeds the computation of the number of such places, used in [`AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed`](thm.html#AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_divisor_eq_max_ord_sub_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : F) (hx : Transcendental K x) (a : K) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (v.ord (x - algebraMap K F a)) := by sorry
