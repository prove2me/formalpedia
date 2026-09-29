-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
-- name    : AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/40611fc7-9a3c-5cf1-9df8-c037da709ad9
-- title:
--   e(w∣ v) equals the ramification index of the fibre centre
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structures forming a scalar tower, and assume $F'/F$ is finite-dimensional and separable. Let $v$ be a place of $F$ over $K$, that is, a valuation subring $\mathcal O_v$ of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring; let $w$ be such a place of $F'$ over $K$, and assume $w$ restricts to $v$, i.e. the preimage of $\mathcal O_w$ under $F \to F'$ is exactly $\mathcal O_v$. Write $C =$ `integralClosureAt F' v` for the integral closure of $\mathcal O_v$ in $F'$, a Dedekind domain with fraction field $F'$ and finite over $\mathcal O_v$, and let `Place.fiberCenter F' v hw` be the height-one prime of $C$ cut out by $w$, namely the centre of $w$ on $C$. The assertion is that `w.ramificationIndex F`, defined as the least positive natural number $n$ for which $w.\mathrm{ord}$ takes the value $n$ at the image in $F'$ of some nonzero element of $F$, coincides with the ramification index, in the sense of `ramificationIdx'`, of the maximal ideal $\mathfrak m_v$ of $\mathcal O_v$ relative to the prime ideal underlying that fibre centre.
--
--   This is the valuation half of the dictionary between the places of $F'$ lying over a place $v$ of $F$ and the primes of the integral closure of $\mathcal O_v$ in $F'$; it is what allows the fundamental identity $\sum_i e_i f_i = [F' : F]$ for Dedekind extensions to be read as a statement about places. It is used in the computation of norms and of local contributions along a fibre, for instance in [`AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber`](thm.html#AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber) and [`AlgebraicCurve.Place.hasValue_norm_along_of_separableAlong`](thm.html#AlgebraicCurve.Place.hasValue_norm_along_of_separableAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter.lean

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) {w : Place K F'}
    (hw : w.restrict F = v) :
    w.ramificationIndex F = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' (Place.fiberCenter F' v hw).asIdeal := by sorry
