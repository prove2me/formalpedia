-- Prove2me | Theorems.Thm_ActuarialValuation_annualReserve_one_step
-- name    : ActuarialValuation.annualReserve_one_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:29:45.15889+00:00
-- url     : https://prove2.me/theorems/2fa43d69-d544-411b-824b-db07c5fd5498
-- title:
--   Conditional annual prospective reserve recursion
-- statement:
--   Where both current and following-year conditional reserves exist, the classical premium-plus-reserve recursion holds.
--
--   **Mathematical statement**
--
--   $$
--   V_t+\pi=v(q_tb+p_tV_{t+1})
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualProspectiveReserve
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem annualReserve_one_step {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (v : ℝ) (n t : ℕ) (b π : ℝ) (ht : t < n) (hS : 0 < annualSurvivalMass P K t)
  (hNext : 0 < annualSurvivalMass P K (t + 1))
  :
  annualProspectiveReserve P K v n t b π + π =
    v * (annualDeathMass P K t / annualSurvivalMass P K t * b +
      annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t *
        annualProspectiveReserve P K v n (t + 1) b π) := by sorry

end ActuarialValuation
