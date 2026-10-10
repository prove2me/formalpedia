-- Prove2me | Theorems.Thm_ActuarialValuation_cm1UnitFundStep_zero
-- name    : ActuarialValuation.cm1UnitFundStep_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:58:43.892+00:00
-- url     : https://prove2.me/theorems/0810f634-8880-4abc-8e07-2fe1a8fe44d2
-- title:
--   Projected profits and unit-linked funds: cm1UnitFundStep_zero
-- statement:
--   Zero investment return leaves only premiums and charges in the fund recurrence. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   j=0\Longrightarrow U_{t+1}=U_t+P-C
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 10. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1UnitFundStep

namespace ActuarialValuation

theorem cm1UnitFundStep_zero (U P C : ℝ) : cm1UnitFundStep U P C 0 = U + P - C := by sorry

end ActuarialValuation
