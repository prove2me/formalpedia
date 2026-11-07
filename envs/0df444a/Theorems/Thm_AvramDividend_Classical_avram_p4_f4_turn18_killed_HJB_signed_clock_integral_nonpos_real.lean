-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn18_killed_HJB_signed_clock_integral_nonpos_real
-- name    : AvramDividend.Classical.avram_p4_f4_turn18_killed_HJB_signed_clock_integral_nonpos_real
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T14:25:45.369208+00:00
-- url     : https://prove2.me/theorems/bc6f30da-8136-438a-956f-bc9ecce53011
-- title:
--   Original stopped Lévy killed HJB signed real-time generator budget
-- statement:
--   The original stopped physical surplus has nonpositive discounted HJB generator residual integrated over the bounded real-time interval, on exactly the positive-reserve and cap-interior cells.
-- source:
--   Original Levy generator HJB sign with corrected two-sided exit clocks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn18_killed_HJB_signed_clock_integral_nonpos_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (b : ℝ) (n : ℕ) :
    ∀ ω : Ω,
      let τ : Ω → ℝ≥0∞ := fun η =>
        min (twoSidedExitUpTimeCorrected X (b - 1) η)
          (min (twoSidedExitDownTimeCorrected X (-1) η) (n : ℝ≥0∞))
      (∫ s : ℝ in Icc (0 : ℝ) (n : ℝ),
        if ENNReal.ofReal s < τ ω ∧
          0 < 1 + X.X (Real.toNNReal s) ω ∧
          ENNReal.ofReal (1 + X.X (Real.toNNReal s) ω) < C then
          Real.exp (-(q * s)) *
            (X.generator w (1 + X.X (Real.toNNReal s) ω) -
              q * w (1 + X.X (Real.toNNReal s) ω))
        else 0) ≤ 0 := by sorry
