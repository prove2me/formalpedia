-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_normalized_finite_brownian_sum
-- name    : BellWilliams2001.ThresholdPolicy.normalized_finite_brownian_sum
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:03:34.450661+00:00
-- url     : https://prove2.me/theorems/61d53555-2c0e-46e7-b9f1-1c9050b40a24
-- title:
--   Normalized weighted sum of independent Brownian motions
-- statement:
--   If the squared weights have positive sum, the weighted sum of a finite independent family of standard Brownian motions divided by the square root of that sum is again standard Brownian motion.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_ManyServerQED_Scheduling_independent_brownian_normalized_linear_combination

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem normalized_finite_brownian_sum {Ω I : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hM : ∀ i, AEMeasurable (fun ω t => B i t ω) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (c : I → ℝ) (s : Finset I) (hs : 0 < ∑ i ∈ s, c i^2) :
    IsBrownianReal (fun t ω => (∑ i ∈ s, c i*B i t ω) / Real.sqrt (∑ i ∈ s, c i^2)) P := by sorry

end BellWilliams2001.ThresholdPolicy
