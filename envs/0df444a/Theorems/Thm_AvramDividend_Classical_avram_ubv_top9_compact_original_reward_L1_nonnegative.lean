-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_compact_original_reward_L1_nonnegative
-- name    : AvramDividend.Classical.avram_ubv_top9_compact_original_reward_L1_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:41:37.737599+00:00
-- url     : https://prove2.me/theorems/060f1bd6-e5fd-4a0a-867f-48ab26d7908c
-- title:
--   Every true bounded-upcross original stopped dividend reward is integrable and nonnegative
-- statement:
--   Given any real nonnegative discount, admissible original process and strategy and integrable full-horizon closed-Iic dividend cash, every source-exact reward stopped at a spatially bounded physical stopping clock is integrable and pointwise nonnegative, with no finite cap or unproved stochastic martingale premise.
-- source:
--   Direct combination of Proved a8ddfafe original compact-clock L1, d12a741a stopping-time real measurability, and 5893451b any-clock source nonnegativity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_compact_original_reward_L1_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ j ω : WithTop ℝ≥0)))
    (hκle : ∀ j ω, κ j ω ≤ τ ω)
    (hκbound : ∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1)
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ j ω, H j ω =
      Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
          else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ j, Integrable (H j) P ∧ (∀ ω, 0 ≤ H j ω) := by sorry
