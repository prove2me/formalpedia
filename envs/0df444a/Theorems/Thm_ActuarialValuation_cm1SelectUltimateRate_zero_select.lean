-- Prove2me | Theorems.Thm_ActuarialValuation_cm1SelectUltimateRate_zero_select
-- name    : ActuarialValuation.cm1SelectUltimateRate_zero_select
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:59:55.758471+00:00
-- url     : https://prove2.me/theorems/8803af27-70d0-41bd-97da-4623d2f108c1
-- title:
--   Select, UDD and constant force: cm1SelectUltimateRate_zero_select
-- statement:
--   A select period of zero years uses ultimate rates immediately. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   k=0\Longrightarrow q=q^U
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 6. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SelectUltimateRate

namespace ActuarialValuation

theorem cm1SelectUltimateRate_zero_select (select : ℕ → ℕ → ℝ) (ultimate : ℕ → ℝ) (x t : ℕ) : cm1SelectUltimateRate select ultimate x 0 t = ultimate (x+t) := by sorry

end ActuarialValuation
