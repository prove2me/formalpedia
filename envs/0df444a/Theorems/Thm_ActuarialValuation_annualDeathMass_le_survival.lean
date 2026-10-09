-- Prove2me | Theorems.Thm_ActuarialValuation_annualDeathMass_le_survival
-- name    : ActuarialValuation.annualDeathMass_le_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:15:33.698397+00:00
-- url     : https://prove2.me/theorems/6c985b29-7623-4adc-925d-3206e5cba01d
-- title:
--   Death requires prior survival
-- statement:
--   Death during policy year t is included in the event of being alive at its start.
--
--   **Mathematical statement**
--
--   $$
--   D_t\le S_t
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem annualDeathMass_le_survival {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K) (t : ℕ)
  :
  annualDeathMass P K t ≤ annualSurvivalMass P K t := by sorry

end ActuarialValuation
