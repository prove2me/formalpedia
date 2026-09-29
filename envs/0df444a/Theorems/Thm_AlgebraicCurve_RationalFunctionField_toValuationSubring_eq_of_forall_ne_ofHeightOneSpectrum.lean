-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
-- name    : AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/b16d57bd-64f3-5e5d-9a5b-eee948a2c874
-- title:
--   Places of K(t)/K other than the finite ones lie at infinity
-- statement:
--   Let $K$ be a field and let $v$ be a place of the rational function field $\mathrm{RatFunc}\,K$ over $K$ in the sense of the project structure `Place`: a datum consisting of a valuation subring $v.\mathrm{toValuationSubring}$ of $\mathrm{RatFunc}\,K$ which contains the image of $K$ under the structure map, which is not the whole field, and which is a principal ideal ring. Assume that for every height-one prime $w$ of the polynomial ring $K[X]$ the place $v$ differs from `Place.ofHeightOneSpectrum w`, the place whose valuation subring is that of the $w$-adic valuation of $K[X]$ extended to its fraction field $\mathrm{RatFunc}\,K$. The conclusion is an equality of subrings of $\mathrm{RatFunc}\,K$: $v.\mathrm{toValuationSubring}$ equals the valuation subring of Mathlib's valuation at infinity `RatFunc.inftyValuation K`, i.e. the ring of rational functions whose numerator degree does not exceed its denominator degree. The hypothesis is a statement about places, not merely about valuation subrings, and the conclusion identifies only the subring, not a normalised valuation.
--
--   This is the classification of the places of the rational function field $K(t)$ trivial on $K$ (the function-field analogue of Ostrowski's theorem): the finite places come from the height-one primes of $K[X]$, and the remaining one is the place at infinity. It is used in the divisor-theoretic treatment of $\mathbb{P}^1$, where it feeds the computation of the degree of the place at infinity and of the order function attached to it at that place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean

import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by sorry
