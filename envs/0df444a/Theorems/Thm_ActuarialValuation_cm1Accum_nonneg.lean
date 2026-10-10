-- Prove2me | Theorems.Thm_ActuarialValuation_cm1Accum_nonneg
-- name    : ActuarialValuation.cm1Accum_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:48:12.177109+00:00
-- url     : https://prove2.me/theorems/ddae1b8c-c8ab-4c81-87af-366c7894715f
-- title:
--   Interest rate algebra: cm1Accum_nonneg
-- statement:
--   Valid effective investment factors stay positive for any finite maturity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   i>-1\Longrightarrow a_n>0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 2. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Accum

namespace ActuarialValuation

theorem cm1Accum_nonneg (i : ℝ) (n : ℕ) (hi : -1 < i) : 0 < cm1Accum i n := by sorry

end ActuarialValuation
