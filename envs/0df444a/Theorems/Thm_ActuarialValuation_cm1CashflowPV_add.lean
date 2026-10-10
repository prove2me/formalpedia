-- Prove2me | Theorems.Thm_ActuarialValuation_cm1CashflowPV_add
-- name    : ActuarialValuation.cm1CashflowPV_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:55:44.740627+00:00
-- url     : https://prove2.me/theorems/c44f589f-cd82-4afc-a73e-b6fe51fc33ae
-- title:
--   General cashflows and loan balances: cm1CashflowPV_add
-- statement:
--   Net present value is linear in the monetary cashflows when discounted on the same basis. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V_{a+b}=V_a+V_b
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV

namespace ActuarialValuation

theorem cm1CashflowPV_add (a b : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1CashflowPV (fun k => a k+b k) n i = cm1CashflowPV a n i + cm1CashflowPV b n i := by sorry

end ActuarialValuation
