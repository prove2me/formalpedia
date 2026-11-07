-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_right_payment_secant_from_gradient
-- name    : AvramDividend.Classical.avram_sweep16_20261106_original_right_payment_secant_from_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:54:14.463518+00:00
-- url     : https://prove2.me/theorems/72adc5af-2db0-4219-87bd-79a5b601cd1d
-- title:
--   Exact original dividend right-payment secant from closed-cap gradient and pre/post reserve range including zero
-- statement:
--   For every actual admissible capped original Lévy strategy, the time-zero or pre-ruin right dividend atom is bounded by the candidate-value drop, using only physical post-payment solvency, pre-payment cap bound, and closed-cap gradient secant. This is an exact source lemma for closing the canonical corrected UBV verification without an extra hjump assumption.
-- source:
--   SWEEP16 downstream original-process boundary closure from independently Proved cap and postpayment reserve bounds, right-jump decomposition and closed-cap secant.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_original_right_payment_secant_from_gradient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))  := by sorry
