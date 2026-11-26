-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_epoch_donsker
-- name    : BellWilliams2001.ThresholdPolicy.renewal_epoch_donsker
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:37:47.519396+00:00
-- url     : https://prove2.me/theorems/5b77a744-639f-478c-8e22-fd6a36296324
-- title:
--   Donsker’s theorem for standardized renewal duration epochs
-- statement:
--   For an independent identically distributed mean-one duration sequence, positive variance gives a standard Brownian limit for the polygonal standardized epoch walk. With zero variance every duration equals one almost everywhere.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_DurrettProbability_donsker

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem renewal_epoch_donsker {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (V : ℕ → Ω → ℝ) (hm : ∀ j, Measurable (V j)) (hind : iIndepFun V P)
    (hid : ∀ j, IdentDistrib (V j) (V 0) P P) (hLp : MemLp (V 0) 2 P)
    (hmean : ∫ ω, V 0 ω ∂P = 1) (B : ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    let a := variance (V 0) P
    (0 < a → TendstoInDistribution (fun n : ℕ =>
      DurrettProbability.walkPath (fun j ω => (V j ω - 1)/Real.sqrt a) n)
      atTop (DurrettProbability.brownianPath B) (fun _ => P) P') ∧
    (a = 0 → ∀ᵐ ω ∂P, ∀ j : ℕ, V j ω = 1) := by sorry

end BellWilliams2001.ThresholdPolicy
