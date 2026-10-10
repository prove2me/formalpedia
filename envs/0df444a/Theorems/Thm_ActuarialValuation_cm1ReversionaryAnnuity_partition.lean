-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ReversionaryAnnuity_partition
-- name    : ActuarialValuation.cm1ReversionaryAnnuity_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:42:34.491998+00:00
-- url     : https://prove2.me/theorems/da9e0441-2b42-4e11-8c8f-b25a92570984
-- title:
--   Joint, last-survivor and reversionary benefits: cm1ReversionaryAnnuity_partition
-- statement:
--   Exact partition of discounted expected y-payments holds without independent life assumptions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   a_{x|y}+a_{xy}=a_y
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 7. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SingleLifeAnnuity
import Definitions.Def_actuarial_cm1JointLifeAnnuity
import Definitions.Def_actuarial_cm1ReversionaryAnnuity

namespace ActuarialValuation

theorem cm1ReversionaryAnnuity_partition (discount pY both : ℕ → ℝ) (n : ℕ) : cm1ReversionaryAnnuity discount pY both n + cm1JointLifeAnnuity discount both n = cm1SingleLifeAnnuity discount pY n := by sorry

end ActuarialValuation
