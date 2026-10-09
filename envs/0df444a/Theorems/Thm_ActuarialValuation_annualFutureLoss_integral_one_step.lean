-- Prove2me | Theorems.Thm_ActuarialValuation_annualFutureLoss_integral_one_step
-- name    : ActuarialValuation.annualFutureLoss_integral_one_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:22:32.193647+00:00
-- url     : https://prove2.me/theorems/b39a00f9-139b-4b2b-a1bc-90aa2a182de0
-- title:
--   Unconditional expected annual cashflow recursion
-- statement:
--   Taking expectation of the pathwise recurrence avoids conditioning on an impossible next-year survival event.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[L_t]+\pi S_t=v(bD_t+\mathbb E[L_{t+1}])
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualFutureLoss
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem annualFutureLoss_integral_one_step {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (v : ℝ) (n t : ℕ) (b π : ℝ) (ht : t < n)
  :
  (∫ ω, annualFutureLoss K v n t b π ω ∂P) +
    π * annualSurvivalMass P K t =
    v * (b * annualDeathMass P K t +
      ∫ ω, annualFutureLoss K v n (t + 1) b π ω ∂P) := by sorry

end ActuarialValuation
