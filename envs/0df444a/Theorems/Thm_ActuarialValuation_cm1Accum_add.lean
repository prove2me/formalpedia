-- Prove2me | Theorems.Thm_ActuarialValuation_cm1Accum_add
-- name    : ActuarialValuation.cm1Accum_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:47:56.603981+00:00
-- url     : https://prove2.me/theorems/0dacb94a-0690-4756-9d31-2ccbc39907f9
-- title:
--   Interest rate algebra: cm1Accum_add
-- statement:
--   Compound accumulation is multiplicative across sequential periods. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   a_{m+n}=a_ma_n
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 2. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Accum

namespace ActuarialValuation

theorem cm1Accum_add (i : ℝ) (m n : ℕ) : cm1Accum i (m+n) = cm1Accum i m * cm1Accum i n := by sorry

end ActuarialValuation
