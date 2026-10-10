-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ProfitGap_add
-- name    : ActuarialValuation.cm1ProfitGap_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:58:41.881262+00:00
-- url     : https://prove2.me/theorems/16157376-29f4-4c27-b8ea-a45313ba28b8
-- title:
--   Bond pricing and immunisation: cm1ProfitGap_add
-- statement:
--   Combining cashflow tranches preserves the surplus of assets over liabilities. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_{a+b,l+m}=S_{a,l}+S_{b,m}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1ProfitGap

namespace ActuarialValuation

theorem cm1ProfitGap_add (a b l m : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1ProfitGap (fun k => a k+b k) (fun k => l k+m k) n i = cm1ProfitGap a l n i + cm1ProfitGap b m n i := by sorry

end ActuarialValuation
