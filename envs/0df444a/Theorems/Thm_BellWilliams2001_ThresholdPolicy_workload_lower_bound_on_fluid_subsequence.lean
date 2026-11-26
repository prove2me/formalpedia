-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_lower_bound_on_fluid_subsequence
-- name    : BellWilliams2001.ThresholdPolicy.workload_lower_bound_on_fluid_subsequence
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:34:28.388576+00:00
-- url     : https://prove2.me/theorems/edddf788-c436-4542-8d43-2992fbedd3f6
-- title:
--   Fluid allocation convergence implies the Brownian cost lower bound
-- statement:
--   Consider a subsequence along which the fluid-scaled capacity allocations converge uniformly on compact intervals in probability to the nominal allocation. The liminf of the expected discounted holding costs on that subsequence is at least the Brownian benchmark $J^*$.
--
--   The limiting fluid allocation gives deterministic service time changes in the joint renewal functional central limit theorem. The capacity balance writes the diffusion-scaled workload as centered input plus a nondecreasing idle-time term. A one-dimensional reflected version of the input is then a pathwise lower bound on the workload. The holding-cost ordering converts this into a lower bound on instantaneous holding costs, and Fatou's lemma passes that bound to discounted expectations.
-- source:
--   Bell and Williams (2001), The Annals of Applied Probability 11(3), 608–649, https://doi.org/10.1214/aoap/1015345343, Section 9, lower bound for Theorem 5.3 after Lemma 9.3

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem workload_lower_bound_on_fluid_subsequence {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (T : ℕ → Allocation Ω) (hT : ∀ n, M.IsAdmissible n (T n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hfluid : UocInProb M.P (fun n ω t => M.Tbar (φ n) (T (φ n)) ω t) M.fluidAllocation)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B) :
    M.Jstar P' B ≤ liminf (fun n => M.cost (φ n) (T (φ n))) atTop := by sorry

end BellWilliams2001.ThresholdPolicy
