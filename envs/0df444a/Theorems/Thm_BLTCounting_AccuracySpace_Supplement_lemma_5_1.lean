-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_lemma_5_1
-- name    : BLTCounting.AccuracySpace.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:03:54.455891+00:00
-- url     : https://prove2.me/theorems/8645b3cf-c45c-49dc-a70b-c7d5f564f705
-- title:
--   Lemma 5.1 — Circle error bounds every finite Laurent coefficient error
-- statement:
--   Let $0<\rho<1$, let $g$ be a complex rational function with no poles on $|z|=\rho$, and let $a[k]$ be its bilateral Laurent coefficients in the annulus containing that circle. The squared circle-error integrand is integrable. If $E_\rho(g)\le E$, then for every integer $N\ge1$,
--   $$\sum_{k=0}^{N-1}|a[k]-f[k]|^2\le\rho^{-2(N-1)}E.$$
--   The coefficients are computed through the normalized Fourier integrals, so they are tied to $g$ and include all negative Laurent indices. No analyticity inside the circle is required. This transfers circle error to finite coefficient error with the exact factor.
--
--   Differences from the source:
--   - encoding: Laurent expansion on an annulus containing the circle → bilateral coefficients computed by Fourier integrals on that circle; reason: these are the unique Laurent coefficients for a rational function without circle poles
--   - encoding: integral and explicit N-term coefficient sum; norm subscript mixes n,N → integrability in the conclusion and the explicit N-term sum with (ρ^(2(N−1)))⁻¹; reason: integrability follows from no circle poles; the written sum fixes the horizon and the exact factor is unchanged
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 5.1, printed p. 31 (PDF p. 32)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_CircleApproximation

namespace BLTCounting.AccuracySpace.Supplement

/-- Lemma 5.1, PDF p.32. N rather than the stray n in the printed norm subscript controls the sum.
Laurent coefficients are computed bilaterally by Fourier integrals; interior poles are allowed.
Interval integrability is a conclusion supplied by rationality and absence of circle poles. -/
theorem lemma_5_1 (ρ E : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (g : RatFunc ℂ)
    (hpole : NoPoleOnCircle g ρ) (herr : circleError g ρ ≤ E) :
    IntervalIntegrable (circleErrorIntegrand g ρ) MeasureTheory.volume (-Real.pi) Real.pi ∧
    ∀ N : ℕ, 1 ≤ N →
      (∑ k ∈ Finset.range N, ‖laurentCoeff g ρ (k : ℤ) - sqrtSeq k‖ ^ 2) ≤
        (ρ ^ (2 * (N - 1)))⁻¹ * E := by sorry

end BLTCounting.AccuracySpace.Supplement
