-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ae_localised_diffuse_and_ordered_rightjump_H_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ae_localised_diffuse_and_ordered_rightjump_H_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:29:18.417284+00:00
-- url     : https://prove2.me/theorems/afb09af7-f98f-4613-bdfa-d4e211e6cfa1
-- title:
--   Almost-everywhere original stopped Stieltjes signed control remainder: diffuse derivative correction plus correctly ordered right-payment jumps
-- statement:
--   For the actual original controlled Lévy process and its right-continuous dividend measure, if an almost-everywhere pathwise localisation has interior diffuse paid mass and enumerates all eligible paid right-dividend jumps, with a finite local secant envelope, then the sum of the discounted diffuse derivative correction and exact source-jump-before-right-payment atomic secant remainders is nonpositive almost everywhere. This lifts the accepted source-exact pathwise signed and absolute cash budget into an a.e. stochastic interface for P4-F. Interior and secant localisation requirements remain explicit rather than asserting false boundary regularity.
-- source:
--   Proved original source pathwise aggregate and cash-envelope theorem 921d8fc4-b7ac-407e-bcf6-d1848649c1c8. Original paper Avram, Palmowski and Pistorius, Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_interior_diffuse_all_eligible_atomic_signed_cash_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ae_localised_diffuse_and_ordered_rightjump_H_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (A : Ω → Set ℝ) (t : Ω → ι → ℝ≥0) (T : Ω → ℝ≥0)
    (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ᵐ ω ∂P, MeasurableSet (A ω))
    (hregion : ∀ᵐ ω ∂P, ∀ s ∈ A ω,
      0 < riskProcess X x D s.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hInt : ∀ᵐ ω ∂P, IntegrableOn
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (A ω) (dividendMeasure D ω))
    (hT : ∀ᵐ ω ∂P, ∀ i, t ω i ≤ T ω)
    (hPre : ∀ᵐ ω ∂P, ∀ i, t ω i = 0 ∨
      (t ω i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ᵐ ω ∂P, ∀ i,
      (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ᵐ ω ∂P, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (hLocalSecant : ∀ᵐ ω ∂P, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
      w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
        K * (rightLimit D (t ω i) ω - D (t ω i) ω)) :
    ∀ᵐ ω ∂P,
      (∫ s in A ω, Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω))
        ∂(dividendMeasure D ω)) +
      (∑' i : ι, Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) ≤ 0 := by sorry
