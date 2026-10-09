-- Prove2me | Theorems.Thm_ActuarialValuation_prospectiveTermReserve_scaling
-- name    : ActuarialValuation.prospectiveTermReserve_scaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:56:56.383014+00:00
-- url     : https://prove2.me/theorems/80c07922-eaa8-43e7-b0a4-bf7ef1b5ac27
-- title:
--   Reserves are homogeneous in cashflow amounts
-- statement:
--   Scaling benefit and premium amounts by the same constant scales the resulting reserve.
--
--   **Mathematical statement**
--
--   $$
--   V_t(cb,c\pi)=cV_t(b,\pi)
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_prospectiveTermReservePV
open MeasureTheory

namespace ActuarialValuation

theorem prospectiveTermReserve_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n t : ℕ)
    (b π c : ℝ)
    :
    prospectiveTermReservePV P K v n t (c * b) (c * π) =
      c * prospectiveTermReservePV P K v n t b π := by sorry

end ActuarialValuation
