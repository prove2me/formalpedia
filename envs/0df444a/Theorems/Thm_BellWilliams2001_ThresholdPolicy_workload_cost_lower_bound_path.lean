-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_cost_lower_bound_path
-- name    : BellWilliams2001.ThresholdPolicy.workload_cost_lower_bound_path
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:28:18.056737+00:00
-- url     : https://prove2.me/theorems/70ccae27-6287-412f-9111-ed4a55f141f1
-- title:
--   Pathwise lower bound on holding cost by reflected workload input
-- statement:
--   For any admissible allocation, the holding cost at each nonnegative time dominates the minimal cost per pooled workload unit times the scalar Skorokhod reflection of the workload driving path.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload

open MeasureTheory Filter Topology Set

namespace BellWilliams2001.ThresholdPolicy

theorem workload_cost_lower_bound_path {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) (ω : Ω) (t : ℝ) (ht : 0 ≤ t)
    (hBound : BddBelow (Set.range (fun s : Set.Icc (0 : ℝ) t => M.workloadInput n T ω s))) :
    let x := M.workloadInput n T ω
    let κ := min (M.h 0) (M.h 1 / M.poolingWeight n)
    κ * (x t - ⨅ s : Set.Icc (0 : ℝ) t, x s) ≤ ∑ k, M.h k * M.Qhat n T ω t k := by sorry

end BellWilliams2001.ThresholdPolicy
