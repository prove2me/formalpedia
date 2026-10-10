-- Prove2me | Theorems.Thm_ActuarialValuation_cm1AnnuityImmediate_succ
-- name    : ActuarialValuation.cm1AnnuityImmediate_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:52:32.534085+00:00
-- url     : https://prove2.me/theorems/f3f2dbaf-2b96-4382-955b-8be363fe31ab
-- title:
--   Annuity certain identities: cm1AnnuityImmediate_succ
-- statement:
--   One added arrears payment is correctly discounted for an additional year. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   a_{n+1}=a_n+v^{n+1}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 3. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1AnnuityImmediate

namespace ActuarialValuation

theorem cm1AnnuityImmediate_succ (i : ℝ) (n : ℕ) : cm1AnnuityImmediate i (n+1) = cm1AnnuityImmediate i n + cm1Discount i (n+1) := by sorry

end ActuarialValuation
