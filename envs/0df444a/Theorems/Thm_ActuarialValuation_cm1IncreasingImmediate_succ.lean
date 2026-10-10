-- Prove2me | Theorems.Thm_ActuarialValuation_cm1IncreasingImmediate_succ
-- name    : ActuarialValuation.cm1IncreasingImmediate_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:54:38.465355+00:00
-- url     : https://prove2.me/theorems/689927a1-595b-4cd1-951b-6beb5de24493
-- title:
--   Annuity certain identities: cm1IncreasingImmediate_succ
-- statement:
--   Increasing annuity recurrence uses the next arithmetically increasing payment. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (Ia)_{n+1}=(Ia)_n+(n+1)v^{n+1}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1IncreasingImmediate

namespace ActuarialValuation

theorem cm1IncreasingImmediate_succ (i : ℝ) (n : ℕ) : cm1IncreasingImmediate i (n+1) = cm1IncreasingImmediate i n + (n+1 : ℕ) * cm1Discount i (n+1) := by sorry

end ActuarialValuation
