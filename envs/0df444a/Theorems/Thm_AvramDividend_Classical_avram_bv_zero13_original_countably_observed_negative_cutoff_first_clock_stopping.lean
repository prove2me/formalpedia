-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_countably_observed_negative_cutoff_first_clock_stopping
-- name    : AvramDividend.Classical.avram_bv_zero13_original_countably_observed_negative_cutoff_first_clock_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:16:11.080144+00:00
-- url     : https://prove2.me/theorems/6b07c30d-49dc-486a-866f-7e6d50b3cf27
-- title:
--   Original finite BV activity countably observed first negative jump detection is a right-continuous stopping time
-- statement:
--   For the actual original bounded-variation finite-negative-activity Levy process, enumerate deterministic observation times and negative mark cutoffs. At each observation time the original intrinsic physical negative jump count above that cutoff is real-valued and right-continuous-filtration measurable. Gate the deterministic time by whether this count is positive, otherwise infinity. The infimum over all cutoffs and observation times is a stopping time for the original right-continuous filtration. No unrelated process or probability space is used. Identification with the actual first negative jump time needs a separately justified dense observation scheme and cadlag finite-activity count equality.
-- source:
--   Necessary original-filtration first-negative-jump localisation interface for finite-negative-activity zero-reserve stopped cash, derived directly from Proved physical marked cutoff past-count adaptation b44d1aa2 and IsStoppingTime.iInf.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_countably_observed_negative_cutoff_first_clock_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (r : ℕ → ℝ≥0) :
    let pastCount : ℕ → ℕ → Ω → ℝ :=
      fun n k ω =>
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 =>
            (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (r k) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ⨅ n : ℕ, ⨅ k : ℕ,
        if 0 < pastCount n k ω
        then (r k : WithTop ℝ≥0) else ⊤) := by sorry
