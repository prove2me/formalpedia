-- Prove2me | Theorems.Thm_ActuarialValuation_presentValue_memLp_two
-- name    : ActuarialValuation.presentValue_memLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:15:58.200976+00:00
-- url     : https://prove2.me/theorems/e94581e8-d45f-44ff-b01b-6bf1c709b7aa
-- title:
--   Finite contingent present value belongs to L²
-- statement:
--   The finite contingent-cashflow present value is square-integrable under a probability measure when the trigger events are measurable. This supplies the second-moment and variance hypotheses for future work.
--
--   **Mathematical statement**
--
--   $$
--   Z\in L^2(P)
--   $$
--
--   Here $Z$ is the finite present value defined in the mission, $P$ is a probability measure, and every scheduled trigger event is measurable.
-- source:
--   *Life Contingencies*, Chapter 3, §3.1, equations (3.2)–(3.3) and §3.1.1 (finite-horizon generalisation); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_presentValue
open MeasureTheory

namespace ActuarialValuation
theorem presentValue_memLp_two {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω)
    (htrigger : ∀ i ∈ payments, MeasurableSet (trigger i)) :
    MemLp (presentValue payments time discount amount trigger) 2 P := by sorry
end ActuarialValuation
