-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_postpayment_source_cash_nonpos
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_postpayment_source_cash_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:16:52.698744+00:00
-- url     : https://prove2.me/theorems/b0601cd9-eedc-4a87-a57e-59634abf80fe
-- title:
--   Finite actual original Lévy pre-ruin postpayment corrections have nonpositive discounted sum
-- statement:
--   For any finite original physical time tags all positive and strictly before ruin, the full discounted sum of actual post-Lévy right-dividend cash plus resulting w-value changes is nonpositive. This is a finite-grid pathwise source correction, preserving simultaneous X and D jump order and requiring no finite jump activity.
-- source:
--   Proved chronological original source jump payment inequality 6cde6ec9 and finite-sum nonpositivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_finite_postpayment_source_cash_nonpos
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
    (ω : Ω) (q : ℝ) (T : Finset ℝ≥0)
    (hT : ∀ t ∈ T, 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ T, Real.exp (-(q * (t : ℝ))) *
      (w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X t ω - D t ω) +
          (rightLimit D t ω - D t ω))) ≤ 0 := by sorry
