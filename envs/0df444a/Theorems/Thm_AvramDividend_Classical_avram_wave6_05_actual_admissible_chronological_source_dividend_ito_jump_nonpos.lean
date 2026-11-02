-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos
-- name    : AvramDividend.Classical.avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:51:12.563133+00:00
-- url     : https://prove2.me/theorems/6cde6ec9-dda6-46bb-a8c4-1d132e2d89ec
-- title:
--   Original admissible same-time source Lévy jump then right dividend payment: exact nonlinear Itô split and nonpositive cash correction
-- statement:
--   At every strictly positive time before original ruin and for any admissible capped dividend strategy, the nonlinear controlled Itô jump of the postpayment test splits exactly into the source-left jump first and chronological right-dividend jump second. The dividend's cash plus test drop is nonpositive without any extra hjump premise, by the already Proved positive-time full-cap secant theorem. Both source and dividend may jump simultaneously, and the payment may exhaust the remaining reserve or reach cap. No finite-jump dividend control assumption.
-- source:
--   Combine the accepted original-source chronological Ito jump correction (14ce41c4-e590-4615-8a70-43f2a0f5d25c) with the accepted original positive-time full-cap dividend w jump-drop (ae7cd7bc-a0a8-4602-bcbd-2d743f9b670b). The bridge identifies riskProcess and its post-dividend subtraction with the original source/after-payment expressions by ring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_positive_time_original_dividend_jump_w_drop
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_chronological_ito_jump_correction

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hPre : (t : ℝ≥0∞) < ruinTime X x D ω) :
    let before : ℝ :=
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω
    let afterSource : ℝ := x + X.X t ω - D t ω
    let afterPayment : ℝ := x + X.X t ω - rightLimit D t ω
    let sourceJump : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let paymentAtom : ℝ := rightLimit D t ω - D t ω
    (w afterPayment - w before -
        deriv w before * (sourceJump - paymentAtom) =
      (w afterSource - w before - deriv w before * sourceJump) +
        (w afterPayment - w afterSource + deriv w before * paymentAtom)) ∧
      w afterPayment - w afterSource + paymentAtom ≤ 0 := by sorry
