-- Prove2me | Theorems.Thm_ActuarialValuation_annualSurvivalMass_partition
-- name    : ActuarialValuation.annualSurvivalMass_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:17:08.062107+00:00
-- url     : https://prove2.me/theorems/20461d4f-49d2-4115-a894-6515fc894a39
-- title:
--   One-year death-survival partition
-- statement:
--   The in-force event partitions into death during the year or survival to the next year.
--
--   **Mathematical statement**
--
--   $$
--   S_t=D_t+S_{t+1}
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem annualSurvivalMass_partition {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K) (t : ℕ)
  :
  annualSurvivalMass P K t = annualDeathMass P K t + annualSurvivalMass P K (t + 1) := by sorry

end ActuarialValuation
