-- Prove2me | Theorems.Thm_ActuarialValuation_cm1CashflowPV_add_last
-- name    : ActuarialValuation.cm1CashflowPV_add_last
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:56:20.41428+00:00
-- url     : https://prove2.me/theorems/36d1d666-34b0-4a08-ac47-d1af6b805231
-- title:
--   General cashflows and loan balances: cm1CashflowPV_add_last
-- statement:
--   Extending a dated cashflow ledger appends precisely one discounted cashflow. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V_{n+1}=V_n+c_nv^{n+1}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1CashflowPV

namespace ActuarialValuation

theorem cm1CashflowPV_add_last (c : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1CashflowPV c (n+1) i = cm1CashflowPV c n i + c n * cm1Discount i (n+1) := by sorry

end ActuarialValuation
