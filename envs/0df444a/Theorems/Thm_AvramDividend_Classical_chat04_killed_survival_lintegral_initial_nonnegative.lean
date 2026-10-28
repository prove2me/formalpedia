-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_initial_nonnegative
-- name    : AvramDividend.Classical.chat04_killed_survival_lintegral_initial_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:19:31.667011+00:00
-- url     : https://prove2.me/theorems/115a9cae-b7dd-4330-b424-2fc89573a8e5
-- title:
--   Killed discounted q-scale renewal identity at horizon zero from nonnegative capital
-- statement:
--   For nonnegative initial reserve, survival over the horizon consisting only of time zero is certain. The discounted q-scale payoff at this horizon equals W(x) by X(0)=0 and exp(0)=1, so its expected ENNReal payoff equals ENNReal.ofReal (W x). This handles the t=0 boundary case of the killed renewal identity.
-- source:
--   Zero-horizon base case of the Open AvramDividend.Classical.chat04_unbounded_killed_survival_discounted_scale_expectation (a885f0b3-3960-424d-97e4-abbcffe268ba), needed for the killed martingale and unbounded two-sided exit parent aed50a34. The complementary negative-reserve case is authored as chat04_killed_survival_lintegral_zero_of_negative_initial_reserve.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_survival_lintegral_initial_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ (0 : ℝ≥0) → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * ((0 : ℝ≥0) : ℝ))) * W (x + X.X 0 ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by sorry
