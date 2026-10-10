-- Prove2me | Theorems.Thm_ActuarialValuation_cm1CAREFundingRate_cancel
-- name    : ActuarialValuation.cm1CAREFundingRate_cancel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:55:13.541852+00:00
-- url     : https://prove2.me/theorems/dea53ef7-db96-45d1-8179-5d4f6d0f2ecd
-- title:
--   DC contribution accumulation and matching: cm1CAREFundingRate_cancel
-- statement:
--   The actuarially equivalent salary contribution rate accumulates exactly to the target retirement liability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   A_n(c^*)=L_{\rm CARE}
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1DCFund
import Definitions.Def_actuarial_cm1CAREFundingRate

namespace ActuarialValuation

theorem cm1CAREFundingRate_cancel (salary revalue growth : ℕ → ℝ) (n : ℕ) (a annuity : ℝ) (hF : cm1AccumulatedSalaryBase salary growth n ≠ 0) : cm1DCFund salary growth n (cm1CAREFundingRate salary revalue growth n a annuity) = cm1CARELiability salary revalue n a annuity := by sorry

end ActuarialValuation
