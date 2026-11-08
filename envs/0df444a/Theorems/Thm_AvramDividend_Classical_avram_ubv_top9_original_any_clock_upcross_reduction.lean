-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_upcross_reduction
-- name    : AvramDividend.Classical.avram_ubv_top9_original_any_clock_upcross_reduction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:52:33.055967+00:00
-- url     : https://prove2.me/theorems/97285f38-ca22-4b02-ac3e-b180d1beda54
-- title:
--   Source-exact infinite-cap stopped expectation from compact spatial Ito budgets
-- statement:
--   Any genuine compact spatial HJB stopped mean upper bound for the original source-exact stopped rewards transfers to the unlocalised finite-horizon source reward by constructing physical upcross clocks, obtaining actual integrability and applying nonnegative Fatou. The local compact HJB budget is explicitly isolated as the remaining stochastic obligation; no uniform-integrability hypothesis is needed.
-- source:
--   Proved physical upcross b2e939f7, compact original reward L1 060f1bd6, and nonnegative exact Fatou transfer 9ce77e93.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_any_clock_upcross_reduction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ T)
    (hCashρI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hLocalBudget : ∀ (κ : ℕ → Ω → ℝ≥0)
      (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ j ω : WithTop ℝ≥0)))
      (hκle : ∀ j ω, κ j ω ≤ ρ ω)
      (hκbound : ∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1)
      (H : ℕ → Ω → ℝ),
      (∀ j ω, H j ω =
        Real.exp (-(q * (κ j ω : ℝ))) *
          w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
            else riskProcess X x D (κ j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) →
      ∀ j, (∫ ω, H j ω ∂P) ≤ w x) :
    (∫ ω, F ω ∂P) ≤ w x := by sorry
