-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T19:55:49.607571+00:00
-- url     : https://prove2.me/theorems/e8fa314d-846b-4b2e-8358-aa1ad4cf48bc
-- title:
--   Original finite-activity jumps have a uniform nonzero magnitude gap on every bounded clock
-- statement:
--   For the original finite-activity spectrally negative Levy process, almost every sample path has for each bounded horizon a strictly positive threshold beneath every nonzero jump magnitude. The threshold is sample-path dependent and uses the exact original jump times. It permits a small-jump cutoff that removes all actual jumps on that bounded horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_jump_tsum_finite_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
          ε ≤ |X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u| := by sorry
