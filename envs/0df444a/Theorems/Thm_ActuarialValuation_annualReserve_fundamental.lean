-- Prove2me | Theorems.Thm_ActuarialValuation_annualReserve_fundamental
-- name    : ActuarialValuation.annualReserve_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:30:18.092785+00:00
-- url     : https://prove2.me/theorems/a832600e-33c0-47d2-aa3e-51f1ae57e2fa
-- title:
--   Annual reserve recursion and death-survival capstone
-- statement:
--   Combines conditional death-survival normalisation with the prospective premium reserve recurrence.
--
--   **Mathematical statement**
--
--   $$
--   q_t+p_t=1,\qquad V_t+\pi=v(q_tb+p_tV_{t+1})
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualProspectiveReserve
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem annualReserve_fundamental {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (v : ℝ) (n t : ℕ) (b π : ℝ) (ht : t < n) (hS : 0 < annualSurvivalMass P K t)
  (hNext : 0 < annualSurvivalMass P K (t + 1))
  :
  (annualDeathMass P K t / annualSurvivalMass P K t +
    annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t = 1)
  ∧ (annualProspectiveReserve P K v n t b π + π =
    v * (annualDeathMass P K t / annualSurvivalMass P K t * b +
      annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t *
        annualProspectiveReserve P K v n (t + 1) b π)) := by sorry

end ActuarialValuation
