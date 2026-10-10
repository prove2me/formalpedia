-- Prove2me | Theorems.Thm_ActuarialValuation_cm1LifeDecrement_telescoping
-- name    : ActuarialValuation.cm1LifeDecrement_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:56:16.665991+00:00
-- url     : https://prove2.me/theorems/ae1d147c-09e6-47b9-b605-9e15d6c060bf
-- title:
--   Life tables and survival composition: cm1LifeDecrement_telescoping
-- statement:
--   Annual cohort deaths sum to the total reduction in survivor counts over the complete interval. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \sum_{k<n}d_{x+k}=l_x-l_{x+n}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 5. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeDecrement

namespace ActuarialValuation

theorem cm1LifeDecrement_telescoping (l : ℕ → ℝ) (x n : ℕ) : (∑ k ∈ Finset.range n, cm1LifeDecrement l x k) = l x - l (x+n) := by sorry

end ActuarialValuation
