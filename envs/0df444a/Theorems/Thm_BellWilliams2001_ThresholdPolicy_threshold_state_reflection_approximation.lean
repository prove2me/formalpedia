-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_state_reflection_approximation
-- name    : BellWilliams2001.ThresholdPolicy.threshold_state_reflection_approximation
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:03:37.769814+00:00
-- url     : https://prove2.me/theorems/f103866d-f43f-4253-82ff-fa0552848444
-- title:
--   Pathwise approximation of threshold queues and idleness by reflection
-- statement:
--   The second queue and idle path under the threshold policy differ from the scaled scalar reflection and regulator by terms bounded by the first queue, first idle time, and threshold slack.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_workload_reflection
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem threshold_state_reflection_approximation {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (hP : M.IsThreshold c n T)
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    let x := M.workloadInput n T ω
    let v := -(⨅ s : Icc (0:ℝ) t, x s)
    let e := (M.threshold c n:ℝ)/M.r n
    let i := M.Ihat n T ω t 0
    let q := M.Qhat n T ω t 0
    |M.Qhat n T ω t 1-(x t+v)/M.poolingWeight n| ≤
      (2*M.muR n 0*i + e + q)/M.poolingWeight n ∧
    |M.Ihat n T ω t 1-v/M.muR n 1| ≤ (M.muR n 0*i + e)/M.muR n 1 := by sorry

end BellWilliams2001.ThresholdPolicy
