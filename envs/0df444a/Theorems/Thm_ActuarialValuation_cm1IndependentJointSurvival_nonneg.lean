-- Prove2me | Theorems.Thm_ActuarialValuation_cm1IndependentJointSurvival_nonneg
-- name    : ActuarialValuation.cm1IndependentJointSurvival_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:00:09.650264+00:00
-- url     : https://prove2.me/theorems/2394f190-5422-4c3f-aa64-28e7d309b251
-- title:
--   Joint, last-survivor and reversionary benefits: cm1IndependentJointSurvival_nonneg
-- statement:
--   The independent-lives product is nonnegative for valid marginal survival probabilities. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p_xp_y\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 7. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1IndependentJointSurvival

namespace ActuarialValuation

theorem cm1IndependentJointSurvival_nonneg (pX pY : ℕ → ℝ) (t : ℕ) (hx : 0 ≤ pX t) (hy : 0 ≤ pY t) : 0 ≤ cm1IndependentJointSurvival pX pY t := by sorry

end ActuarialValuation
