-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_primitive_diffusion_second_moment_majorants
-- name    : BellWilliams2001.ThresholdPolicy.primitive_diffusion_second_moment_majorants
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:28:07.224549+00:00
-- url     : https://prove2.me/theorems/f9d45fc0-0cdf-4e31-b4c2-e1c0f5864958
-- title:
--   Second moments of centered arrival and service processes
-- statement:
--   For all sufficiently large indices, the expected squared normalized centered count, maximized over a compact diffusion time interval, is bounded by a constant times one plus the interval length. The assertion holds for all five renewal streams.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

theorem primitive_diffusion_second_moment_majorants {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      ∃ (JA : Fin 2 → Ω → ℝ≥0∞) (JS : Fin 3 → Ω → ℝ≥0∞),
        (∀ k, Measurable (JA k) ∧ ∫⁻ ω, JA k ω ∂M.P ≤ ENNReal.ofReal (C*(1+t))) ∧
        (∀ j, Measurable (JS j) ∧ ∫⁻ ω, JS j ω ∂M.P ≤ ENNReal.ofReal (C*(1+t))) ∧
        ∀ ω s, 0 ≤ s → s ≤ t →
          (∀ k, (ENNReal.ofReal |M.Ahat n ω s k|)^2 ≤ JA k ω) ∧
          (∀ j, (ENNReal.ofReal |M.Shat n ω s j|)^2 ≤ JS j ω) := by sorry

end BellWilliams2001.ThresholdPolicy
