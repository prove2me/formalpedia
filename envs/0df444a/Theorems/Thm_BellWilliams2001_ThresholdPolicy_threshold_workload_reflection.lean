-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_workload_reflection
-- name    : BellWilliams2001.ThresholdPolicy.threshold_workload_reflection
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:07:22.850773+00:00
-- url     : https://prove2.me/theorems/095c4d5e-faae-5c58-ac6d-1a1f5042969b
-- title:
--   The threshold workload satisfies the scalar reflection bound with slack Lʳ/r
-- statement:
--   For an admissible threshold allocation, the weighted idle time of server 2 lies between the running regulator of its input and that regulator plus Lʳ/r. The input includes the first server’s weighted idle time. The threshold policy makes server 2 busy whenever the workload exceeds Lʳ/r.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Section 8, workload reflection and equation (163)

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold

open Set

namespace BellWilliams2001.ThresholdPolicy

theorem threshold_workload_reflection {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (hP : M.IsThreshold c n T)
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (hZero : M.serverTwoInput n T ω 0 = 0)
    (hBound : BddBelow (Set.range (fun s : Set.Icc (0 : ℝ) t => M.serverTwoInput n T ω s))) :
    let v := -(⨅ s : Set.Icc (0 : ℝ) t, M.serverTwoInput n T ω s)
    v ≤ M.muR n 1 * M.Ihat n T ω t 1 ∧
      M.muR n 1 * M.Ihat n T ω t 1 ≤ v + (M.threshold c n : ℝ) / M.r n := by sorry

end BellWilliams2001.ThresholdPolicy
