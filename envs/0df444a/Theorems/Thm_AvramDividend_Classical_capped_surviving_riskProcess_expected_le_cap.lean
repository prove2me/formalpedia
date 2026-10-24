-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_surviving_riskProcess_expected_le_cap
-- name    : AvramDividend.Classical.capped_surviving_riskProcess_expected_le_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:59:48.650383+00:00
-- url     : https://prove2.me/theorems/07852adc-33f7-40e5-9c99-58c48acaa797
-- title:
--   Expected surviving reserve at a positive time is bounded by the admissibility cap
-- statement:
--   For a capped admissible strategy at any strictly positive deterministic time t, the extended-real expectation of the controlled reserve, restricted to survival beyond t, is at most the cap C. On surviving sample paths admissibility gives ofReal(U_t)<=C; on the others the integrand is zero. Integrate the pointwise bound against the probability measure. This provides a finite terminal-reserve localisation bound whenever C is finite, without imposing a stochastic-generator hypothesis or a dividend countability restriction.
-- source:
--   Definitions.Def_AvramDividend_Classical_DividendStrategy (IsAdmissibleLe and riskProcess); SpectrallyNegativeLevy.isProbability; Mathlib.MeasureTheory.Integral.Lebesgue.Basic (lintegral_mono and lintegral_const).

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_surviving_riskProcess_expected_le_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ ω, if (t : ℝ≥0∞) < ruinTime X x D ω then
      ENNReal.ofReal (riskProcess X x D t ω) else 0 ∂P) ≤ C := by sorry
