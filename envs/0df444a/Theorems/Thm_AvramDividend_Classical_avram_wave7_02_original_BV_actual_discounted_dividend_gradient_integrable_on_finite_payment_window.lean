-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:31:19.17697+00:00
-- url     : https://prove2.me/theorems/017e0847-9b36-4c3f-9981-6f35d097cc93
-- title:
--   Actual pre-ruin BV discounted Stieltjes dividend-gradient integral is integrable on a finite payment window under local derivative bound
-- statement:
--   For original X and genuine IsDividendStrategy D, on any measurable subset of the actual pre-ruin paymentTimes window bounded by a finite horizon, the Stieltjes dividend measure has finite mass. If the physical discounted derivative integrand is strongly measurable and its undiscouned C1 derivative is uniformly bounded on that subset, nonnegative q and physical time ensure the exponential factor is at most one. Therefore the original real Stieltjes dividend-gradient correction is integrable. Exact original riskProcess, ruinTime, paymentTimes and dividendMeasure are used.
-- source:
--   Proved original dividendMeasure_paymentWindow_finite_of_strategy and pinned Mathlib IntegrableOn.of_bound; pathwise exponential and derivative inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
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
    (hApos : ∀ t ∈ A, 0 ≤ t)
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
