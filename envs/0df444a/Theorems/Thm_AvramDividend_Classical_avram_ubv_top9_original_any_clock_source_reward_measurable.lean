-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_source_reward_measurable
-- name    : AvramDividend.Classical.avram_ubv_top9_original_any_clock_source_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:43:34.563166+00:00
-- url     : https://prove2.me/theorems/05fe4611-e856-4173-b21e-e49c44146e1d
-- title:
--   Exact original physical stopped post-right terminal plus closed dividend cash is measurable
-- statement:
--   For every genuine right-continuous stopping clock and original dividend strategy, the actual discounted terminal plus full closed-Iic discounted Stieltjes dividend reward is measurable, including zero-clock and ruin branch conventions.
-- source:
--   Proved d12a741a real stopping-time measurability, 06433bf3 source W measurability, 2d478c7d closed-Iic cash measurability and p4_c zero-negative payoff measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_any_clock_source_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    Measurable F := by sorry
