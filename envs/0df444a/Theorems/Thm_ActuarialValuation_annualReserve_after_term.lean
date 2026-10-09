-- Prove2me | Theorems.Thm_ActuarialValuation_annualReserve_after_term
-- name    : ActuarialValuation.annualReserve_after_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:25:50.90318+00:00
-- url     : https://prove2.me/theorems/6160c444-d35a-4025-9356-afaeddd1f19a
-- title:
--   No future reserve beyond maturity
-- statement:
--   With no future payment the ratio is numerically zero, including the totalised zero-denominator case.
--
--   **Mathematical statement**
--
--   $$
--   t\ge n\Rightarrow V_t=0
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualProspectiveReserve
open MeasureTheory

namespace ActuarialValuation

theorem annualReserve_after_term {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (v : ℝ) (n t : ℕ) (b π : ℝ) (ht : n ≤ t)
  :
  annualProspectiveReserve P K v n t b π = 0 := by sorry

end ActuarialValuation
