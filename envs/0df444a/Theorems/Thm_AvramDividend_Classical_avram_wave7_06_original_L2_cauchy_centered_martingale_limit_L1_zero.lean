-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:42:34.347336+00:00
-- url     : https://prove2.me/theorems/05634bad-3f1f-49b7-8d34-85215f9918f5
-- title:
--   Original Levy probability L2 Cauchy centred martingale limit preserves zero L1 expectation
-- statement:
--   For the exact original spectral-negative Levy source P, any Cauchy sequence in its real L2(P) space whose members each have zero actual P expectation has a real L2(P) limit with zero P expectation. The source structure supplies the probability measure assumption, L2 completeness supplies a limit, and the already Proved original-space L2 expectation continuity transfers zero mean. No stronger uniform-integrability hypothesis is needed once the required source L2 Cauchy bound has been proved.
-- source:
--   W7-06 original-source small-jump truncation limit/expectation handoff: rigorous abstract L2 to L1 mean passage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hCauchy : CauchySeq M)
    (hCentered : ∀ n, (∫ ω, M n ω ∂P) = 0) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by sorry
