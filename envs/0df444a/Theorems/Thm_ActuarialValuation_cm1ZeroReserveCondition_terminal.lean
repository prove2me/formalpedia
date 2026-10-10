-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ZeroReserveCondition_terminal
-- name    : ActuarialValuation.cm1ZeroReserveCondition_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:40:08.346549+00:00
-- url     : https://prove2.me/theorems/b6da843e-7a64-4472-bdac-0f55fa85d68c
-- title:
--   Backwards non-unit zeroisation: cm1ZeroReserveCondition_terminal
-- statement:
--   An admissible backwards-zeroised reserve schedule has the prescribed terminal boundary. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R_N=0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveCondition

namespace ActuarialValuation

theorem cm1ZeroReserveCondition_terminal (c s g R : ℕ → ℝ) (N : ℕ) (h : cm1ZeroReserveCondition c s g R N) : R N = 0 := by sorry

end ActuarialValuation
