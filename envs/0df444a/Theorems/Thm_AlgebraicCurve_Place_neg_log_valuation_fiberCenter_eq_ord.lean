-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_neg_log_valuation_fiberCenter_eq_ord
-- name    : AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/21c6a547-aee6-56dd-bc98-198e58dd8f83
-- title:
--   Order at a place equals valuation at its fibre centre
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields (with compatible $K$-algebra structures, so that $F'$ is an $F$-algebra and a scalar tower over $K$), with $F'/F$ finite-dimensional and separable. Let $v$ be a place of $F$ over $K$ and $w$ a place of $F'$ over $K$ — that is, a valuation subring of the field containing the image of $K$, distinct from the whole field, and a principal ideal ring — and assume $w$ lies over $v$ in the sense that $w.\mathrm{restrict}\,F = v$, i.e. the contraction of the valuation subring of $w$ along $F \to F'$ is the valuation subring of $v$. Let $C_v$ denote the integral closure of the valuation ring of $v$ in $F'$, a Dedekind domain with fraction field $F'$ and finite over the valuation ring of $v$, and let $P_w =$ `fiberCenter F' v hw` be the height-one prime of $C_v$ obtained as the centre of $w$ in $C_v$ (the contraction of the maximal ideal of the valuation ring of $w$). Then for every nonzero $x \in F'$, minus the logarithm of the $P_w$-adic valuation of $x$, taken in $\mathbb{Z}^{m0}$ on the fraction field $F'$, equals $w.\mathrm{ord}\,x$, the integer order of $x$ at $w$, itself defined as minus the logarithm of the valuation `w.adicValuation` attached to $w$.
--
--   This is the valuation dictionary between places of $F'$ above a place $v$ of $F$ and the height-one primes of the integral closure of the valuation ring of $v$: the normalised order function of the place coincides with the $P_w$-adic valuation. It makes the ramification theory of Dedekind domains available for computing place-theoretic orders, and is used for the description of the powers of $P_w$ in terms of $\mathrm{ord}_w$ in [`AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter`](thm.html#AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_neg_log_valuation_fiberCenter_eq_ord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'} (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) : -WithZero.log ((Place.fiberCenter F' v hw).valuation F' x) = w.ord x := by sorry
