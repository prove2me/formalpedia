-- Prove2me | Theorems.Thm_ActuarialValuation_cm1LifeMortality_nonneg
-- name    : ActuarialValuation.cm1LifeMortality_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:54:39.270086+00:00
-- url     : https://prove2.me/theorems/7795e7d3-a87e-4e4c-87ee-3721e87fb8e0
-- title:
--   Life tables and survival composition: cm1LifeMortality_nonneg
-- statement:
--   The probability of death during a term cannot be negative when life counts decrease. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   {}_nq_x\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 5. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeMortality

namespace ActuarialValuation

theorem cm1LifeMortality_nonneg (l : ℕ → ℝ) (x n : ℕ) (hl : 0 < l x) (hle : l (x+n) ≤ l x) : 0 ≤ cm1LifeMortality l x n := by sorry

end ActuarialValuation
