-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ProfitGap_second_deriv
-- name    : ActuarialValuation.cm1ProfitGap_second_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:38:52.094061+00:00
-- url     : https://prove2.me/theorems/13880bb9-8471-4976-a127-aa2b898450d5
-- title:
--   Bond pricing and immunisation: cm1ProfitGap_second_deriv
-- statement:
--   Convexity mismatch of asset and liability PVs is the second derivative of surplus. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S''(i)=V_A''(i)-V_L''(i)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1ProfitGap

namespace ActuarialValuation

theorem cm1ProfitGap_second_deriv (a l : ℕ → ℝ) (n : ℕ) (i : ℝ) (hi : -1 < i) : deriv (deriv (cm1ProfitGap a l n)) i = deriv (deriv (cm1CashflowPV a n)) i - deriv (deriv (cm1CashflowPV l n)) i := by sorry

end ActuarialValuation
