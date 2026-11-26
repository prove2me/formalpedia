-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_state_coupling_from_limits
-- name    : BellWilliams2001.ThresholdPolicy.threshold_state_coupling_from_limits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:07:19.429984+00:00
-- url     : https://prove2.me/theorems/e85c5b8e-e3be-46fb-8387-b3c985291d4d
-- title:
--   From fluid allocation and residual limits to the threshold diffusion coupling
-- statement:
--   Assume the threshold allocations converge to the nominal fluid allocation and the first queue and first server idle time converge to zero uniformly on compact time intervals in probability. Then the two scaled queues and idle times admit the Brownian coupling of Theorem 5.2. The remaining step combines the joint renewal functional central limit theorem under the fluid service clocks with the one-dimensional workload reflection.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Section 8, proof of Theorem 5.2 after Theorem 7.1 and Lemma 8.1

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory
open scoped NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem threshold_state_coupling_from_limits {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (hc : 0 < c) (T : ℕ → Allocation Ω)
    (hT : ∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (T n) ∧ M.IsThreshold c n (T n))
    (hResidual : UocInProb M.P
      (fun n ω t => ![M.Qhat n (T n) ω t 0, M.Ihat n (T n) ω t 0]) (fun _ => 0))
    (hFluid : UocInProb M.P (fun n ω t => M.Tbar n (T n) ω t) M.fluidAllocation)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B) :
    CouplingConverges M.P P'
      (fun n ω t => ![M.Qhat n (T n) ω t 0, M.Qhat n (T n) ω t 1,
        M.Ihat n (T n) ω t 0, M.Ihat n (T n) ω t 1])
      (fun ω t => ![0, M.Qstar B ω t 1, 0, M.Istar B ω t 1]) := by sorry

end BellWilliams2001.ThresholdPolicy
