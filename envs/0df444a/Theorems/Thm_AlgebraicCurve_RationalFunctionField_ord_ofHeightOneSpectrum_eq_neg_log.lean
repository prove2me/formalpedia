-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
-- name    : AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/2bd8c823-9b6f-5635-a092-45542aa65bd1
-- title:
--   Order at a finite place of K(t) equals the adic valuation
-- statement:
--   Let $K$ be a field, let $w$ be a height-one prime of the polynomial ring $K[X]$, let $p \in K[X]$ be nonzero with $w.\mathrm{asIdeal} = (p)$, and let $f \in \mathrm{RatFunc}\,K$ be nonzero. Attached to $w$ is the place `Place.ofHeightOneSpectrum w` of $\mathrm{RatFunc}\,K$ over $K$, namely the $K$-subalgebra-containing valuation subring of $\mathrm{RatFunc}\,K$ cut out by the $\mathbb{Z}^{m0}$-valued $w$-adic valuation $w.\mathrm{valuation}\,(\mathrm{RatFunc}\,K)$, together with the facts that this subring is not all of $\mathrm{RatFunc}\,K$ and is a principal ideal ring. For a place $v$, $\mathrm{ord}\,f$ is defined as $-\mathrm{log}$ of the value at $f$ of the adic valuation intrinsically associated with $v$ (the valuation of the height-one prime of the valuation ring of $v$). The assertion is that for this place the intrinsic normalised order of $f$ agrees with the extrinsic one: $$\mathrm{ord}\,f = -\mathrm{log}\bigl(w.\mathrm{valuation}\,(\mathrm{RatFunc}\,K)\,f\bigr),$$ an equality of integers, i.e. $\mathrm{ord}\,f$ is the multiplicity of $p$ in $f$.
--
--   This identifies the normalised order function of a finite place of the rational function field $K(t)$, defined through the place's own valuation ring, with the exponent of the corresponding $w$-adic valuation on $\mathrm{RatFunc}\,K$; it is the computational form in which orders at finite places are used. It is cited by [`AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_of_span`](thm.html#AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_of_span) and by [`AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero`](thm.html#AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) {f : RatFunc K} (hf : f ≠ 0) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord f = -WithZero.log (w.valuation (RatFunc K) f) := by sorry
