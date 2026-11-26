-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_queue_regularity
-- name    : BellWilliams2001.ThresholdPolicy.admissible_queue_regularity
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:07:17.092224+00:00
-- url     : https://prove2.me/theorems/9d2174bc-86bc-5753-906d-c88f0357323a
-- title:
--   Admissible diffusion-scaled queues are càdlàg and measurable at each time
-- statement:
--   For every admissible allocation, each diffusion-scaled queue path is càdlàg on nonnegative time and every fixed-time observation is almost everywhere measurable.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, (9)–(14), (19)

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open MeasureTheory

namespace BellWilliams2001.ThresholdPolicy

theorem admissible_queue_regularity {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) :
    (∀ ω k, IsCadlag (fun t => M.Qhat n T ω t k)) ∧
    (∀ t, 0 ≤ t → ∀ k, AEMeasurable (fun ω => M.Qhat n T ω t k) M.P) := by sorry

end BellWilliams2001.ThresholdPolicy
