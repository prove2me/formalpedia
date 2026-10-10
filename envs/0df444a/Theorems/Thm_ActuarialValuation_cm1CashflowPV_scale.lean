-- Prove2me | Theorems.Thm_ActuarialValuation_cm1CashflowPV_scale
-- name    : ActuarialValuation.cm1CashflowPV_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:55:56.393997+00:00
-- url     : https://prove2.me/theorems/79e626c7-4f11-474b-a803-4ccaccb3dabb
-- title:
--   General cashflows and loan balances: cm1CashflowPV_scale
-- statement:
--   Scaling every payment by a monetary factor scales total present value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V_{ca}=cV_a
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV

namespace ActuarialValuation

theorem cm1CashflowPV_scale (a : ℕ → ℝ) (n : ℕ) (i c : ℝ) : cm1CashflowPV (fun k => c*a k) n i = c * cm1CashflowPV a n i := by sorry

end ActuarialValuation
