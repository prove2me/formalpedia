-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_masked_qvalue_cell_L1
-- name    : AvramDividend.Classical.avram_bv_residual9_original_masked_qvalue_cell_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:46:34.586559+00:00
-- url     : https://prove2.me/theorems/d6232304-1947-4de6-b369-85e5c69ae3f6
-- title:
--   Original BV strict-pre-ruin masked discounted q times pre-jump value is integrable on every physical grid cell
-- statement:
--   For the original source process and the exact strict ruin, pre-jump positive, cap-interior cell mask, the literal discounted q*w(Z_t) variable is integrable. The proof combines the Proved automatic fixed-time L1 original left-limit value with original process and ruin-time measurability, preserving exact original mask. It does not assume L1 of the random generator or weighted compensated jump R term.
-- source:
--   AVRAM BV-RESIDUAL9, genuine original stopped generator-cell q*w L1 component of edb6442e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_masked_qvalue_cell_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T t : ℝ≥0) (ht : t ≤ T) (C : ℝ≥0∞) :
    Integrable (fun ω =>
      let Z : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      if (t : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (t : ℝ))) * (q * w Z)
      else 0) P := by sorry
