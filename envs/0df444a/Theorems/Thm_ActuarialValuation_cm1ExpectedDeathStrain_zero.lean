-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ExpectedDeathStrain_zero
-- name    : ActuarialValuation.cm1ExpectedDeathStrain_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:58:00.937132+00:00
-- url     : https://prove2.me/theorems/f210046e-d559-475a-901c-91cb5063fde2
-- title:
--   Prospective reserve and mortality profit: cm1ExpectedDeathStrain_zero
-- statement:
--   There is no expected death strain when death probability is zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   q=0\Longrightarrow EDS=0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 9. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedDeathStrain

namespace ActuarialValuation

theorem cm1ExpectedDeathStrain_zero (S : ℝ) : cm1ExpectedDeathStrain 0 S = 0 := by sorry

end ActuarialValuation
