-- Prove2me | Theorems.Thm_ActuarialValuation_annualSurvivalMass_zero
-- name    : ActuarialValuation.annualSurvivalMass_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:14:01.157976+00:00
-- url     : https://prove2.me/theorems/6045affd-bdc8-4ac4-ab79-095052dfcb59
-- title:
--   Certain survival at issue
-- statement:
--   Every natural-valued curtate lifetime is at least zero, so the time-zero in-force event is certain.
--
--   **Mathematical statement**
--
--   $$
--   S_0=1
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem annualSurvivalMass_zero {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  :
  annualSurvivalMass P K 0 = 1 := by sorry

end ActuarialValuation
