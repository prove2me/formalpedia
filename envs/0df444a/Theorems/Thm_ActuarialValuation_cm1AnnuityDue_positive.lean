-- Prove2me | Theorems.Thm_ActuarialValuation_cm1AnnuityDue_positive
-- name    : ActuarialValuation.cm1AnnuityDue_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:52:55.167053+00:00
-- url     : https://prove2.me/theorems/12a5c1a3-1a29-433e-bb5b-fc2ded2f429b
-- title:
--   Annuity certain identities: cm1AnnuityDue_positive
-- statement:
--   Nonempty annuities in advance have positive present value for valid discount rates. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   n>0,\ i>-1\Longrightarrow \ddot a_n>0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 3. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1AnnuityDue

namespace ActuarialValuation

theorem cm1AnnuityDue_positive (i : ℝ) (n : ℕ) (hi : -1 < i) (hn : 0 < n) : 0 < cm1AnnuityDue i n := by sorry

end ActuarialValuation
