-- Prove2me | Theorems.Thm_ActuarialValuation_cm1SalaryPensionFunding_fundamental
-- name    : ActuarialValuation.cm1SalaryPensionFunding_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:57:06.671529+00:00
-- url     : https://prove2.me/theorems/451526f4-759d-42de-9403-f870f0573a60
-- title:
--   DC contribution accumulation and matching: cm1SalaryPensionFunding_fundamental
-- statement:
--   Capstone proves the unique actuarially consistent contribution threshold funding a CARE pension, with nonnegative surplus for rates above the threshold. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c^*\ge0,\quad A_n(c^*)=L,\quad c\ge c^*\Rightarrow A_n(c)\ge L
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1DCFund
import Definitions.Def_actuarial_cm1CAREFundingRate
import Definitions.Def_actuarial_cm1FundingSurplus

namespace ActuarialValuation

theorem cm1SalaryPensionFunding_fundamental (salary revalue growth : ℕ → ℝ) (n : ℕ) (accrual annuity : ℝ) (hF : 0 < cm1AccumulatedSalaryBase salary growth n) (hL : 0 ≤ cm1CARELiability salary revalue n accrual annuity) : (0 ≤ cm1CAREFundingRate salary revalue growth n accrual annuity) ∧ (cm1DCFund salary growth n (cm1CAREFundingRate salary revalue growth n accrual annuity) = cm1CARELiability salary revalue n accrual annuity) ∧ (∀ c : ℝ, cm1CAREFundingRate salary revalue growth n accrual annuity ≤ c → 0 ≤ cm1FundingSurplus salary revalue growth n accrual annuity c) := by sorry

end ActuarialValuation
