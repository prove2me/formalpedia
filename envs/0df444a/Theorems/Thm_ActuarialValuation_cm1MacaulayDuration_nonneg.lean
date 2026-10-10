-- Prove2me | Theorems.Thm_ActuarialValuation_cm1MacaulayDuration_nonneg
-- name    : ActuarialValuation.cm1MacaulayDuration_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:00:17.660809+00:00
-- url     : https://prove2.me/theorems/42778cb4-0250-428e-a483-0a9f6064fd6a
-- title:
--   Bond pricing and immunisation: cm1MacaulayDuration_nonneg
-- statement:
--   A positive priced bond with nonnegative cashflows has nonnegative Macaulay duration. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_{\rm Mac}\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1MacaulayDuration

namespace ActuarialValuation

theorem cm1MacaulayDuration_nonneg (c : ℕ → ℝ) (n : ℕ) (i : ℝ) (hi : -1 < i) (hc : ∀ k ∈ Finset.range n, 0 ≤ c k) (hV : 0 < cm1CashflowPV c n i) : 0 ≤ cm1MacaulayDuration c n i := by sorry

end ActuarialValuation
