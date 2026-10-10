-- Prove2me | Theorems.Thm_ActuarialValuation_cm1FundingSurplus_nonnegative_above_rate
-- name    : ActuarialValuation.cm1FundingSurplus_nonnegative_above_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:56:48.337977+00:00
-- url     : https://prove2.me/theorems/787eb471-64b1-4dfb-9e00-e51d3e4d7ad8
-- title:
--   DC contribution accumulation and matching: cm1FundingSurplus_nonnegative_above_rate
-- statement:
--   Contributions at or above the equivalent rate do not underfund the target in this deterministic model. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c\ge c^*\Rightarrow\Delta(c)\ge0
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1CAREFundingRate
import Definitions.Def_actuarial_cm1FundingSurplus

namespace ActuarialValuation

theorem cm1FundingSurplus_nonnegative_above_rate (salary revalue growth : ℕ → ℝ) (n : ℕ) (a annuity c : ℝ) (hF : 0 < cm1AccumulatedSalaryBase salary growth n) (hc : cm1CAREFundingRate salary revalue growth n a annuity ≤ c) : 0 ≤ cm1FundingSurplus salary revalue growth n a annuity c := by sorry

end ActuarialValuation
