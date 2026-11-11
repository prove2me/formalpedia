-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin23_indexed_original_exact_source_reward_measurable
-- name    : AvramDividend.Classical.avram_mix_fin23_indexed_original_exact_source_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:46:22.939779+00:00
-- url     : https://prove2.me/theorems/0f1bc0e5-8fa3-4bb3-8bc1-a5a1c7cc03bd
-- title:
--   Indexed actual original closed-clock top-cap cash and terminal measurability
-- statement:
--   Directly from Proved 05fe4611 any-stopping-time exact stopped payoff theorem, deduce every indexed original stopped reward H_j is measurable. Admissibility projects to the genuine original dividend strategy. This supports root-connected 304898c7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin23_indexed_original_exact_source_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
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
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ j, Measurable (H j) := by sorry
