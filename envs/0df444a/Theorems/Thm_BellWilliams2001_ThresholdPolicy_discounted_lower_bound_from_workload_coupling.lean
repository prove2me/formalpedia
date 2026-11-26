-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_discounted_lower_bound_from_workload_coupling
-- name    : BellWilliams2001.ThresholdPolicy.discounted_lower_bound_from_workload_coupling
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:42:41.792691+00:00
-- url     : https://prove2.me/theorems/e6b1507c-d453-447d-b8b2-76c79f805c5d
-- title:
--   The discounted lower bound from a pooled-workload coupling
-- statement:
--   If a cofinal sequence of admissible prelimit workload inputs has a compact-uniform coupling to the pooled Brownian input, then the liminf of its original costs is at least the Brownian benchmark.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_cost_lower_bound_path
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_discounted_cost_aemeasurable
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_past_infimum_from_dyadic_grid
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open BellWilliams2001.ThresholdPolicy
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem discounted_lower_bound_from_workload_coupling {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (T : ℕ → Allocation Ω) (hT : ∀ n, M.IsAdmissible n (T n))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B)
    (hCouple : CouplingConverges M.P P'
      (fun n ω t => ![M.workloadInput (φ n) (T (φ n)) ω t])
      (fun ω t => ![∑ k, M.yvec k * M.Xtilde B ω t k])) :
    M.Jstar P' B ≤ liminf (fun n => M.cost (φ n) (T (φ n))) atTop := by sorry

end BellWilliams2001.ThresholdPolicy
