-- Prove2me | Theorems.Thm_ActuarialValuation_cm1MacaulayDuration_cancel
-- name    : ActuarialValuation.cm1MacaulayDuration_cancel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:01:07.179128+00:00
-- url     : https://prove2.me/theorems/9b0e249d-9869-47ce-a1cd-88ce7183dc19
-- title:
--   Bond pricing and immunisation: cm1MacaulayDuration_cancel
-- statement:
--   Duration times bond PV gives exactly the time-weighted discounted cashflow total. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_{\rm Mac}V=D_{\rm num}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1DurationNumerator
import Definitions.Def_actuarial_cm1MacaulayDuration

namespace ActuarialValuation

theorem cm1MacaulayDuration_cancel (c : ℕ → ℝ) (n : ℕ) (i : ℝ) (hV : cm1CashflowPV c n i ≠ 0) : cm1MacaulayDuration c n i * cm1CashflowPV c n i = cm1DurationNumerator c n i := by sorry

end ActuarialValuation
