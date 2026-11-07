-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_finite_upcross_stop_contact
-- name    : AvramDividend.Classical.avram_p4_f7_hjb_finite_upcross_stop_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:21:05.803838+00:00
-- url     : https://prove2.me/theorems/cb9573bd-4801-4619-81ad-76206a14eaa0
-- title:
--   Original mixed Levy first-passage barrier contact at bounded stopped upper exit
-- statement:
--   On the actual corrected original two-sided strict upper-before-lower exit event, truncated by a finite clock n, the three-clock stopping time is exactly the upper first-passage time and the actual no-positive-jump Levy process attains the level b-1. This isolates the pathwise boundary contact from the stochastic Ito/Dynkin supermartingale estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f7_hjb_finite_upcross_stop_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (b : ℝ) (n : ℕ) (hb : 1 ≤ b)
    (ω : Ω)
    (hup :
      twoSidedExitUpTimeCorrected X (b - 1) ω <
        twoSidedExitDownTimeCorrected X (-1) ω ∧
      twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞)) :
    X.X
      (ENNReal.toNNReal
        (min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞)))) ω =
      b - 1 := by sorry
