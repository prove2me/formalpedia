-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_payment_window_integrable_discount_gradient_no_time_premise
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_payment_window_integrable_discount_gradient_no_time_premise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:16:25.960444+00:00
-- url     : https://prove2.me/theorems/c3baae2f-a874-42d4-93d9-459d054781fc
-- title:
--   Original BV finite payment window determines nonnegative clock for discounted Stieltjes derivative integrability
-- statement:
--   In the genuine Avram source, every real paymentTimes σ member has nonnegative time, by an already Proved source theorem. Thus the full finite-window Stieltjes dividend-gradient integrability result needs no independent hApos premise when A is contained in paymentTimes of the actual ruin time, with a finite horizon, uniform derivative bound, nonnegative q and strong measurability. This preserves the exact original controlled reserve and dividendMeasure D ω.
-- source:
--   Proved paymentTimes_membership_to_nNReal_active 71123237 combined with Proved 017e0847 finite-window original Stieltjes integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_payment_window_integrable_discount_gradient_no_time_premise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAwindow : A ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
    (K : ℝ) (hK : 0 ≤ K)
    (hDerivativeBound : ∀ t ∈ A,
      |deriv w (riskProcess X x D t.toNNReal ω)| ≤ K)
    (hMeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      ((dividendMeasure D ω).restrict A)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω) := by sorry
