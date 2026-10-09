-- Prove2me | Theorems.Thm_ActuarialValuation_prospectiveTermReserve_at_issue
-- name    : ActuarialValuation.prospectiveTermReserve_at_issue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:52:01.101808+00:00
-- url     : https://prove2.me/theorems/69d31a38-3cfa-428c-975d-dec37182d306
-- title:
--   Reserve at inception is expected loss at issue
-- statement:
--   Every life is in force at the outset, so the survival conditioning denominator is one.
--
--   **Mathematical statement**
--
--   $$
--   V_0=\mathbb E_P[L_{n,0}]
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_futureTermLossPV
import Definitions.Def_actuarial_prospectiveTermReservePV
open MeasureTheory

namespace ActuarialValuation

theorem prospectiveTermReserve_at_issue {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b π : ℝ)
    :
    prospectiveTermReservePV P K v n 0 b π =
      ∫ ω, futureTermLossPV K v n 0 b π ω ∂P := by sorry

end ActuarialValuation
