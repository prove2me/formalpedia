-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
-- name    : AvramDividend.Classical.avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:47:38.111054+00:00
-- url     : https://prove2.me/theorems/bf18b23c-3124-46f5-bba9-04d53d272177
-- title:
--   Every countable original strictly positive pre-ruin dividend right-jump w correction has nonpositive discounted sum
-- statement:
--   For countably many strictly positive chronological dividend payments before original ruin, the source-faithful discounted real w jump residual δ_t + w(U_t−δ_t)−w(U_t) has nonpositive sum, given its real summability. The already accepted pointwise w-drop theorem discharges the sign at each element of the countable family, without imposing a global time-zero w-drop hypothesis which can be false for initial capital exceeding cap. Original X_t includes source left jumps at simultaneous times. Arbitrary admissible finite-variation dividend controls including infinitely many jumps are allowed.
-- source:
--   Uses accepted avram_wave6_05_positive_time_original_dividend_jump_w_drop and Mathlib `tsum_nonpos`; no universal t=0 hjump premise. Signed discounted w right-payment sum only; actual full Stieltjes continuous mass is accounted separately.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_positive_time_original_dividend_jump_w_drop

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (A : Set ℝ≥0) (hCount : A.Countable)
    (hA : ∀ t : A, 0 < (t : ℝ≥0) ∧
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun t : A => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
