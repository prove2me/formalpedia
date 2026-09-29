-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
-- name    : AlgebraicCurve.Place.ord_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e9cbc30c-79d6-5e63-be12-ce80e24a3ecf
-- title:
--   Constants have order of vanishing zero at every place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring `v.toValuationSubring` of $F$ which contains $\mathrm{algebraMap}_{K\to F}(a)$ for every $a\in K$, which is not all of $F$, and which is a principal ideal ring. Attached to $v$ is the valuation `v.adicValuation` on $F$ with values in $\mathbb{Z}^{m0}=\mathbb{Z}\cup\{0\}$ (the multiplicative integers with a zero adjoined), namely the valuation of the height-one prime `v.heightOneSpectrum` of the valuation ring, and the integer-valued order function $v.\mathrm{ord}(f) = -\log\bigl(v.\mathrm{adicValuation}(f)\bigr)$, where `WithZero.log` sends the adjoined zero to $0$. The assertion is that for every $c\in K$ one has $v.\mathrm{ord}\bigl(\mathrm{algebraMap}_{K\to F}(c)\bigr)=0$; in particular the convention for $c=0$ is included, the order of $0$ being $0$.
--
--   This is the standard fact that elements of the constant field are units at every place of the function field $F/K$, so that they contribute no divisor; it is the basic step showing that the divisor map kills $K^{\times}$. It is used pervasively throughout the development of divisors and the divisor class group, and in the estimates for functions on annuli that rely on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 := by sorry
