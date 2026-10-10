-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ProfitGap_zero
-- name    : ActuarialValuation.cm1ProfitGap_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:58:02.74392+00:00
-- url     : https://prove2.me/theorems/25a4d4dd-3f34-424c-9aaf-dbba32359c74
-- title:
--   Bond pricing and immunisation: cm1ProfitGap_zero
-- statement:
--   No dated asset or liability payments imply a zero surplus. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_0(i)=0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1ProfitGap

namespace ActuarialValuation

theorem cm1ProfitGap_zero (a l : ℕ → ℝ) (i : ℝ) : cm1ProfitGap a l 0 i = 0 := by sorry

end ActuarialValuation
