-- Prove2me | Theorems.Thm_ActuarialValuation_cm1DeferredDeath_formula
-- name    : ActuarialValuation.cm1DeferredDeath_formula
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T21:56:37.842123+00:00
-- url     : https://prove2.me/theorems/f5c2c204-5366-4e62-9b96-ae10ef77fa6f
-- title:
--   Life tables and survival composition: cm1DeferredDeath_formula
-- statement:
--   Deferred death probability is a ratio of life-table deaths during the later subinterval. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   {}_{k|n}q_x=(l_{x+k}-l_{x+k+n})/l_x
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 5. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1DeferredDeath

namespace ActuarialValuation

theorem cm1DeferredDeath_formula (l : ℕ → ℝ) (x k n : ℕ) (hx : l x ≠ 0) (hk : l (x+k) ≠ 0) : cm1DeferredDeath l x k n = (l (x+k) - l (x+k+n)) / l x := by sorry

end ActuarialValuation
