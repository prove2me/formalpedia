-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_finite_grid_HJB_signed_cash_bound
-- name    : AvramDividend.Classical.avram_bv_env3_original_finite_grid_HJB_signed_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:21:18.898267+00:00
-- url     : https://prove2.me/theorems/e0c1a8ac-4c8a-4ea0-bb20-db22a79bbe43
-- title:
--   Original BV finite-grid physical HJB residual mean closes full Stieltjes cash
-- statement:
--   Given the exact original-X BV physical-grid stopped generator drift B, a centred integrable compensated martingale M, and the genuine strict prepayment source pathwise inequality, use the original residual sign and source-exact postpayment atom comparison to bound the full closed-horizon ENNReal cash. No conditional source is imported.
-- source:
--   Proved original physical finite-grid HJB signed-mean theorem 6927a23f and Proved any-clock signed strict-to-closed Stieltjes cash theorem 7fb52983.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_finite_grid_HJB_signed_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (M B : Ω → ℝ)
    (hB : ∀ ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      B ω =
        (∑ i ∈ Finset.range n,
          if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u (i + 1) : ℝ) - (u i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range n,
           (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
           else 0) * (R (u i) - R (u (i + 1)))))
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hWitness : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D ⟨T, hT⟩ ω)
       else 0) ≤ w x + M ω + B ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
