-- Prove2me | Theorems.Thm_ActuarialValuation_annualReserve_mass_identity
-- name    : ActuarialValuation.annualReserve_mass_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:24:48.500214+00:00
-- url     : https://prove2.me/theorems/cc40654f-b9ab-43d9-b391-0065a6217d87
-- title:
--   Reserve normalisation by survival mass
-- statement:
--   When survival probability is positive, reserve times that probability equals expected future loss.
--
--   **Mathematical statement**
--
--   $$
--   S_tV_t=\mathbb E[L_t]
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
import Definitions.Def_actuarial_annualProspectiveReserve
import Definitions.Def_actuarial_annualSurvivalMass
open MeasureTheory

namespace ActuarialValuation

theorem annualReserve_mass_identity {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (v : ℝ) (n t : ℕ) (b π : ℝ) (hS : 0 < annualSurvivalMass P K t)
  :
  annualSurvivalMass P K t * annualProspectiveReserve P K v n t b π =
    ∫ ω, annualFutureLoss K v n t b π ω ∂P := by sorry

end ActuarialValuation
