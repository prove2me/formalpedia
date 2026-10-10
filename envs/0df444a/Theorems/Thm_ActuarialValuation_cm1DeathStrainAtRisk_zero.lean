-- Prove2me | Theorems.Thm_ActuarialValuation_cm1DeathStrainAtRisk_zero
-- name    : ActuarialValuation.cm1DeathStrainAtRisk_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:57:51.199584+00:00
-- url     : https://prove2.me/theorems/4ded23c8-6221-4077-b3b1-97537153f864
-- title:
--   Prospective reserve and mortality profit: cm1DeathStrainAtRisk_zero
-- statement:
--   Without any released reserve, death strain equals the full sum assured. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   DSAR=S\text{ if reserve is zero}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 9. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DeathStrainAtRisk

namespace ActuarialValuation

theorem cm1DeathStrainAtRisk_zero (S : ℝ) : cm1DeathStrainAtRisk S 0 = S := by sorry

end ActuarialValuation
