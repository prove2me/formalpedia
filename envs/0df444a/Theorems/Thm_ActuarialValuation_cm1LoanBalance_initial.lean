-- Prove2me | Theorems.Thm_ActuarialValuation_cm1LoanBalance_initial
-- name    : ActuarialValuation.cm1LoanBalance_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:57:29.90913+00:00
-- url     : https://prove2.me/theorems/a97635f6-8ced-4d71-a160-c09a34d1d4fc
-- title:
--   General cashflows and loan balances: cm1LoanBalance_initial
-- statement:
--   Loan outstanding balance at inception is the PV of all due repayments. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B_0=V_c
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 3. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1LoanBalance

namespace ActuarialValuation

theorem cm1LoanBalance_initial (c : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1LoanBalance c n 0 i = cm1CashflowPV c n i := by sorry

end ActuarialValuation
