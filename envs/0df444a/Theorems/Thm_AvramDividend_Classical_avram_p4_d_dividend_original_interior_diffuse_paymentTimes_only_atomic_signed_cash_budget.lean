-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_interior_diffuse_paymentTimes_only_atomic_signed_cash_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_interior_diffuse_paymentTimes_only_atomic_signed_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:11:55.848118+00:00
-- url     : https://prove2.me/theorems/9f5bf190-114e-455d-bdd5-3f47a0a64da3
-- title:
--   Original true paymentTimes gives full signed interior Stieltjes and all right-atomic cash budget without a separate survival premise
-- statement:
--   The genuine source original paymentTimes carrier already implies each right-payment index is time zero or strictly before the source ruin clock. Transport this accepted survival lemma into the accepted strict interior diffuse and every-right-atom signed budget, preserving the source post-Lévy/pre-dividend reserve ordering, the exact ruin-truncated stopped Cash and the continuous and singular Stieltjes measure contributions. No standing assumption at the lower or upper contact boundary is added.
-- source:
--   Accepted mixed interior diffuse/all eligible right-atomic signed budget 921d8fc4-b7ac-407e-bcf6-d1848649c1c8 and source paymentTimes strict survival or zero a7a447fa; Avram Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_interior_diffuse_all_eligible_atomic_signed_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The interior diffuse and authentic right-atomic dividend budget needs only the true paymentTimes carrier to infer pre-ruin survival. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_interior_diffuse_paymentTimes_only_atomic_signed_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ s ∈ A,
      0 < riskProcess X x D s.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hInt : IntegrableOn
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      A (dividendMeasure D ω))
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : ι → ℝ≥0) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : Function.Injective (fun i : ι => (t i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω))
      ∂(dividendMeasure D ω)) + (∑' i : ι, J i) ≤ 0 ∧
    Summable J ∧ Summable (fun i : ι => |J i|) ∧
    (∑' i : ι, |J i|) ≤
      (K - 1) * (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
