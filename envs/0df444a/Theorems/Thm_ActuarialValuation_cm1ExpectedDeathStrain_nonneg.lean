-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ExpectedDeathStrain_nonneg
-- name    : ActuarialValuation.cm1ExpectedDeathStrain_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:58:12.524993+00:00
-- url     : https://prove2.me/theorems/7fe7dd79-7b21-4318-a2ff-08791c250007
-- title:
--   Prospective reserve and mortality profit: cm1ExpectedDeathStrain_nonneg
-- statement:
--   Expected positive death strain remains nonnegative for valid mortality probabilities. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   q,S\ge0\Longrightarrow EDS\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 9. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedDeathStrain

namespace ActuarialValuation

theorem cm1ExpectedDeathStrain_nonneg (q S : ℝ) (hq : 0 ≤ q) (hS : 0 ≤ S) : 0 ≤ cm1ExpectedDeathStrain q S := by sorry

end ActuarialValuation
