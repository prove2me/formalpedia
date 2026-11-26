-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_workload_and_idle_regularity
-- name    : BellWilliams2001.ThresholdPolicy.admissible_workload_and_idle_regularity
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:03:42.520799+00:00
-- url     : https://prove2.me/theorems/8e0643f7-4400-4124-b3fa-ee4d77b672cd
-- title:
--   Regularity of the workload input and diffusion-scaled idle paths
-- statement:
--   Under an admissible allocation, the two diffusion idle paths and the pooled workload input are càdlàg with almost everywhere measurable fixed-time evaluations.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_queue_regularity
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem admissible_workload_and_idle_regularity {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) :
    (∀ ω k, IsCadlag (fun t => M.Ihat n T ω t k)) ∧
    (∀ t, 0 ≤ t → ∀ k, AEMeasurable (fun ω => M.Ihat n T ω t k) M.P) ∧
    (∀ ω, IsCadlag (M.workloadInput n T ω)) ∧
    (∀ t, 0 ≤ t → AEMeasurable (fun ω => M.workloadInput n T ω t) M.P) := by sorry

end BellWilliams2001.ThresholdPolicy
