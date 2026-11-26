-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_allocations_from_vanishing_queues
-- name    : BellWilliams2001.ThresholdPolicy.fluid_allocations_from_vanishing_queues
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:29:51.781517+00:00
-- url     : https://prove2.me/theorems/bdfc5494-199d-56be-b7ca-dbc88ab816e4
-- title:
--   Fluid allocation and idle-time limits from fluid queue collapse
-- statement:
--   Along any cofinal sequence, if admissible allocations have vanishing fluid queues uniformly on compact intervals in probability, then the fluid service clocks converge to the critical allocation and both fluid idle paths vanish in the same sense.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open MeasureTheory Filter Topology Set

namespace BellWilliams2001.ThresholdPolicy

theorem fluid_allocations_from_vanishing_queues {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (T : ℕ → Allocation Ω)
    (hT : ∀ᶠ n in atTop, M.IsAdmissible (φ n) (T n))
    (hq : UocInProb M.P (fun n ω t => M.Qbar (φ n) (T n) ω t) (fun _ => 0)) :
    UocInProb M.P (fun n ω t => M.Tbar (φ n) (T n) ω t) M.fluidAllocation ∧
    UocInProb M.P (fun n ω t => M.Ibar (φ n) (T n) ω t) (fun _ => 0) := by sorry

end BellWilliams2001.ThresholdPolicy
