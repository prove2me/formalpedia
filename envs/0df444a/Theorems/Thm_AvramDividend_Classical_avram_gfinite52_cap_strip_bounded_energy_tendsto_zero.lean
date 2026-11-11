-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite52_cap_strip_bounded_energy_tendsto_zero
-- name    : AvramDividend.Classical.avram_gfinite52_cap_strip_bounded_energy_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:17:20.815833+00:00
-- url     : https://prove2.me/theorems/a8a504eb-45d5-4619-a85e-9061bf222083
-- title:
--   Uniformly bounded cap-strip Gaussian energy vanishes
-- statement:
--   With finite occupation measure, a shrinking cap strip has vanishing L² energy for any coefficient with a uniform pointwise square bound. This converts the cap-strip occupation convergence into the quadratic-variation estimate needed for Gaussian stochastic-isometry control. The first-moment stochastic estimate and original Itô-Stieltjes accounting remain separate obligations.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite52_cap_strip_bounded_energy_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (c : ℝ) (b : ℕ → ℝ) (hbmono : Monotone b)
    (hb : Tendsto b atTop (𝓝 c))
    (hCapNull : μ {ω | c ≤ Y ω} = 0)
    (f : Ω → ℝ) (B : ℝ) (hf2 : ∀ ω, (f ω) ^ 2 ≤ B ^ 2) :
    Tendsto
      (fun j : ℕ => ∫⁻ ω in {ω | b j < Y ω},
        ENNReal.ofReal ((f ω) ^ 2) ∂μ)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  sorry
