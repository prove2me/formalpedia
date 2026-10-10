-- Prove2me | Theorems.Thm_ActuarialValuation_cm1SingleLifeAnnuity_zero
-- name    : ActuarialValuation.cm1SingleLifeAnnuity_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:39:01.839068+00:00
-- url     : https://prove2.me/theorems/55df5727-625a-4b6a-bb07-1fc14dc063a9
-- title:
--   Joint, last-survivor and reversionary benefits: cm1SingleLifeAnnuity_zero
-- statement:
--   A benefit with no scheduled payment dates has zero annuity present value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   a_y(0)=0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 7. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SingleLifeAnnuity

namespace ActuarialValuation

theorem cm1SingleLifeAnnuity_zero (discount survival : ℕ → ℝ) : cm1SingleLifeAnnuity discount survival 0 = 0 := by sorry

end ActuarialValuation
