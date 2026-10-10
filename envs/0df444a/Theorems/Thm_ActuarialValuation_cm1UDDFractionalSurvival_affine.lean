-- Prove2me | Theorems.Thm_ActuarialValuation_cm1UDDFractionalSurvival_affine
-- name    : ActuarialValuation.cm1UDDFractionalSurvival_affine
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:58:15.841982+00:00
-- url     : https://prove2.me/theorems/4d3d8aa5-3b24-4f48-abd2-78bd69b047ef
-- title:
--   Select, UDD and constant force: cm1UDDFractionalSurvival_affine
-- statement:
--   The UDD fractional model is affine in elapsed time, with no assumption that it is multiplicative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p_{s+t}=p_s+p_t-1\text{ under UDD}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 6. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1UDDFractionalSurvival

namespace ActuarialValuation

theorem cm1UDDFractionalSurvival_affine (p s t : ℝ) : cm1UDDFractionalSurvival p (s+t) = cm1UDDFractionalSurvival p s + cm1UDDFractionalSurvival p t - 1 := by sorry

end ActuarialValuation
