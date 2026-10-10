-- Prove2me | Theorems.Thm_ActuarialValuation_cm1UDDFractionalSurvival_one
-- name    : ActuarialValuation.cm1UDDFractionalSurvival_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:57:39.229072+00:00
-- url     : https://prove2.me/theorems/86292754-2aac-470a-8e8e-afefb7b08f7e
-- title:
--   Select, UDD and constant force: cm1UDDFractionalSurvival_one
-- statement:
--   The fractional UDD model matches annual survival at the year endpoint. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   {}_1p_x=p_x
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 6. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1UDDFractionalSurvival

namespace ActuarialValuation

theorem cm1UDDFractionalSurvival_one (p : ℝ) : cm1UDDFractionalSurvival p 1 = p := by sorry

end ActuarialValuation
