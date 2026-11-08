-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_upcross_fatou_budget_transfer
-- name    : AvramDividend.Classical.avram_ubv_top9_original_upcross_fatou_budget_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:48:19.059096+00:00
-- url     : https://prove2.me/theorems/9ce77e93-de41-4541-b9cb-9671c9a3a1fc
-- title:
--   True original infinite-cap arbitrary-clock HJB expected upper from compact budgets by nonnegative Fatou
-- statement:
--   For the exact original stopped dividend reward and a pathwise eventually equal family of source-exact localised stopped rewards, local L1 and genuine expected upper budgets entail the original expected upper inequality without uniform integrability. Full measurability and nonnegativity follow from the original source hypotheses.
-- source:
--   Proved a400dff7 nonnegative Fatou, 8e855eb9 topcap potential positivity, 5893451b any-clock reward positivity and source-exact arbitrary stopping-clock measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_upcross_fatou_budget_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ j ω : WithTop ℝ≥0)))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ j ω, H j ω =
      Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
          else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hHI : ∀ j, Integrable (H j) P)
    (hEventually : ∀ ω, ∀ᶠ j : ℕ in atTop, κ j ω = ρ ω)
    (hBudget : ∀ j, (∫ ω, H j ω ∂P) ≤ w x) :
    (∫ ω, F ω ∂P) ≤ w x := by sorry
