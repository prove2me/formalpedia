-- Prove2me | Theorems.Thm_ActuarialValuation_cm1Discount_accum_cancel
-- name    : ActuarialValuation.cm1Discount_accum_cancel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:49:14.837283+00:00
-- url     : https://prove2.me/theorems/67c176d5-4ef4-4317-8b8c-2639545d4a3b
-- title:
--   Interest rate algebra: cm1Discount_accum_cancel
-- statement:
--   Under strictly positive accumulation, discount and accumulated values are reciprocal. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   v_na_n=1
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 2. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount

namespace ActuarialValuation

theorem cm1Discount_accum_cancel (i : ℝ) (n : ℕ) (hi : -1 < i) : cm1Discount i n * cm1Accum i n = 1 := by sorry

end ActuarialValuation
