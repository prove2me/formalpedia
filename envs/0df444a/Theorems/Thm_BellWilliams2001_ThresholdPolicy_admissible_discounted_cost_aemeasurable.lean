-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_discounted_cost_aemeasurable
-- name    : BellWilliams2001.ThresholdPolicy.admissible_discounted_cost_aemeasurable
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:29:54.226819+00:00
-- url     : https://prove2.me/theorems/7a620389-4500-4285-b338-ff5c3221cbb1
-- title:
--   Joint measurability of the discounted queue holding cost
-- statement:
--   For any admissible allocation, the nonnegative discounted queue holding cost is almost everywhere measurable on the product space, and its integral over time is almost everywhere measurable on the stochastic sample space.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open MeasureTheory Set
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

theorem admissible_discounted_cost_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) :
    let f (ω : Ω) (t : ℝ) := ENNReal.ofReal (Real.exp (-M.gamma*t) * ∑ k, M.h k * M.Qhat n T ω t k)
    AEMeasurable (Function.uncurry f) (M.P.prod (volume.restrict (Ioi (0:ℝ)))) ∧
    AEMeasurable (fun ω => ∫⁻ t in Ioi (0:ℝ), f ω t ∂volume) M.P := by sorry

end BellWilliams2001.ThresholdPolicy
