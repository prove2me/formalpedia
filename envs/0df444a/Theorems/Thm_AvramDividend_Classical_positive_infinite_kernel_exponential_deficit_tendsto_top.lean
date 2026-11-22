-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_infinite_kernel_exponential_deficit_tendsto_top
-- name    : AvramDividend.Classical.positive_infinite_kernel_exponential_deficit_tendsto_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:53:34.764918+00:00
-- url     : https://prove2.me/theorems/105d3abb-1b8f-4a7a-ba22-c121f91a7d6a
-- title:
--   Positive infinite-activity Lévy kernel has compensated Laplace deficit diverging to infinity
-- statement:
--   If a positive-half-line Lévy jump kernel κ is supported on t>0 and has infinite mass even on (0,1], then its compensated exponential deficit ∫(1−exp(−nt))κ(dt) diverges to infinity as natural n→∞, in ENNReal. This follows by reflecting κ under t↦−t and applying the already-Proved original negative-jump exponential deficit divergence e74ed6de, with no need for a finite small-jump first moment. It is the precise diverging-denominator source for the killed Bernstein renewal potential's zero-atom theorem 55603110.
-- source:
--   Proved e74ed6de negative_levy_exponential_deficit_tendsto_top; pinned Mathlib Measure.map_apply, lintegral_map, negative map continuous; source 55603110.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_negative_levy_exponential_deficit_tendsto_top
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_infinite_kernel_exponential_deficit_tendsto_top
    (κ : Measure ℝ)
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (hκinf : κ (Ioc (0 : ℝ) 1) = ⊤) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ t : ℝ, ENNReal.ofReal
          (1 - Real.exp (-((n : ℝ) * t))) ∂κ)
      atTop (𝓝 (⊤ : ℝ≥0∞)) := by sorry
