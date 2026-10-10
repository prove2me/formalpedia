-- Prove2me | Theorems.Thm_ActuarialValuation_cm1AnnuityDue_zero
-- name    : ActuarialValuation.cm1AnnuityDue_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:50:41.133979+00:00
-- url     : https://prove2.me/theorems/1519c03f-1de3-479a-81ff-a93f3b701c61
-- title:
--   Annuity certain identities: cm1AnnuityDue_zero
-- statement:
--   No payment dates means zero annuity-certain value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \ddot a_0=0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 3. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1AnnuityDue

namespace ActuarialValuation

theorem cm1AnnuityDue_zero (i : ℝ) : cm1AnnuityDue i 0 = 0 := by sorry

end ActuarialValuation
