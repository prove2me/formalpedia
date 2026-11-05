-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_initial_right_cash_le_candidate_even_immediate_ruin
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_initial_right_cash_le_candidate_even_immediate_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:39:30.295059+00:00
-- url     : https://prove2.me/theorems/fb1d7c73-2b43-4b6e-8ec4-c107afe418ff
-- title:
--   Original BV C1 time-zero right-dividend is bounded by the candidate even at immediate ruin
-- statement:
--   For the genuine original source process and admissible dividend control with left-continuous/right-payment convention, original BV separate interior C1 derivative floor and w(0) nonnegative establish the exact samplewise initial right dividend bound rightLimit D 0 ω ≤ w x. This remains valid when ruin is immediate and uses the actual first right-payment atom and source X at zero.
-- source:
--   Accepted original time-zero HJB ledger e6bfefd9 and independent BV C1 postpayment nonnegativity 28b04520.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_initial_right_cash_le_candidate_even_immediate_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (ω : Ω) : rightLimit D 0 ω ≤ w x := by sorry
