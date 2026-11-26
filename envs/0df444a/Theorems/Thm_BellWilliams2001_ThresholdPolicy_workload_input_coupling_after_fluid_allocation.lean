-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_input_coupling_after_fluid_allocation
-- name    : BellWilliams2001.ThresholdPolicy.workload_input_coupling_after_fluid_allocation
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:04:53.660491+00:00
-- url     : https://prove2.me/theorems/133ae5d1-a0d7-499a-9e4e-4661b22bfcf5
-- title:
--   Pooled Brownian workload input after fluid service allocation convergence
-- statement:
--   Along any cofinal index sequence with eventually admissible policies and the critical fluid service clocks as a compact-uniform probability limit, the pooled workload input couples to the paper’s projected Brownian input and has a compact interval modulus bound.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem workload_input_coupling_after_fluid_allocation {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (T : ℕ → Allocation Ω) (hT : ∀ᶠ n in atTop, M.IsAdmissible (φ n) (T n))
    (hfluid : UocInProb M.P (fun n ω t => M.Tbar (φ n) (T n) ω t) M.fluidAllocation)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B) :
    CouplingConverges M.P P' (fun n ω t => ![M.workloadInput (φ n) (T n) ω t])
      (fun ω t => ![∑ i, M.yvec i * M.Xtilde B ω t i]) ∧
    (∀ (H : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (H:ℝ), ∃ t ∈ Icc (0:ℝ) (H:ℝ), |s-t| ≤ δ ∧
        ε ≤ |M.workloadInput (φ n) (T n) ω s-M.workloadInput (φ n) (T n) ω t|} ≤ ENNReal.ofReal η) := by sorry

end BellWilliams2001.ThresholdPolicy
