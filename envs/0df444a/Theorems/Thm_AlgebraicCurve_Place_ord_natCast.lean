-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_natCast
-- name    : AlgebraicCurve.Place.ord_natCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e2a0b930-e803-57bb-9cf6-8e5d4e7bd6cd
-- title:
--   Natural-number constants have order zero at a place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the divisor-class-group module: a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Attached to such a $v$ is its adic valuation $v.adicValuation$, the $\mathbb{Z}^{m0}$-valued valuation on $F$ associated with the height-one prime determined by $v$, and the order function $v.\mathrm{ord}(f) = -\mathrm{log}\,(v.adicValuation\,f)$, where $\mathrm{log}$ is the `WithZero` logarithm, so that in particular $v.\mathrm{ord}(0) = 0$ by convention. The assertion is that for every natural number $n$, the image of $n$ in $F$ under the canonical cast satisfies $v.\mathrm{ord}(n) = 0$. No hypothesis on the characteristic of $F$ is imposed: in characteristic $p$ the cast of $n$ may vanish, and the conclusion still holds because of the convention giving $0$ order zero.
--
--   This is the familiar statement that a place of $F$ over $K$ is trivial on constants, specialised to the constants coming from the prime ring; it is used in the computations of orders of differentials, being cited by [`AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one`](thm.html#AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one), [`AlgebraicCurve.Place.ordDiff_D_nonneg`](thm.html#AlgebraicCurve.Place.ordDiff_D_nonneg) and [`AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff`](thm.html#AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_natCast.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_natCast {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (n : ℕ) :
    v.ord (n : F) = 0 := by sorry
