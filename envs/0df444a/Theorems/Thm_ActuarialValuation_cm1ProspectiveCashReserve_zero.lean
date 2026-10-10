-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ProspectiveCashReserve_zero
-- name    : ActuarialValuation.cm1ProspectiveCashReserve_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:56:29.758229+00:00
-- url     : https://prove2.me/theorems/bab44075-bd0e-4546-9396-85e5ead99b5f
-- title:
--   Prospective reserve and mortality profit: cm1ProspectiveCashReserve_zero
-- statement:
--   Without future premium income the prospective reserve is the sum of future benefits and expenses. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V_t|_{P=0}=B+E
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 9. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProspectiveCashReserve

namespace ActuarialValuation

theorem cm1ProspectiveCashReserve_zero (B E : ℝ) : cm1ProspectiveCashReserve B E 0 = B+E := by sorry

end ActuarialValuation
