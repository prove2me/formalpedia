-- Prove2me | Theorems.Thm_ActuarialValuation_annualDeathSurvival_probabilities_sum
-- name    : ActuarialValuation.annualDeathSurvival_probabilities_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:19:03.670487+00:00
-- url     : https://prove2.me/theorems/38f0fcae-6cfb-42cf-aec0-8b26c91e1dbc
-- title:
--   Conditional death and survival probabilities total one
-- statement:
--   Positive current survival probability permits normalisation of the disjoint death and next-year survival probabilities.
--
--   **Mathematical statement**
--
--   $$
--   q_t+p_t=1
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem annualDeathSurvival_probabilities_sum {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K) (t : ℕ) (hS : 0 < annualSurvivalMass P K t)
  :
  annualDeathMass P K t / annualSurvivalMass P K t +
    annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t = 1 := by sorry

end ActuarialValuation
