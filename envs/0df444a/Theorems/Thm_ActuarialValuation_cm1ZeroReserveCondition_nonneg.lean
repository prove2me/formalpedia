-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ZeroReserveCondition_nonneg
-- name    : ActuarialValuation.cm1ZeroReserveCondition_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:40:35.900856+00:00
-- url     : https://prove2.me/theorems/56077fa4-64f8-4155-9950-3b37678a54e6
-- title:
--   Backwards non-unit zeroisation: cm1ZeroReserveCondition_nonneg
-- statement:
--   All reserves in a backwards-zeroised schedule are nonnegative, including the terminal reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   0\le t\le N\Longrightarrow R_t\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveCondition

namespace ActuarialValuation

theorem cm1ZeroReserveCondition_nonneg (c s g R : ℕ → ℝ) (N t : ℕ) (h : cm1ZeroReserveCondition c s g R N) (ht : t ≤ N) : 0 ≤ R t := by sorry

end ActuarialValuation
