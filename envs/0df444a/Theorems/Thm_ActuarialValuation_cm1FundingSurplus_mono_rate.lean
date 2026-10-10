-- Prove2me | Theorems.Thm_ActuarialValuation_cm1FundingSurplus_mono_rate
-- name    : ActuarialValuation.cm1FundingSurplus_mono_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:56:11.156232+00:00
-- url     : https://prove2.me/theorems/873d5c21-8d04-4b2a-a22d-8da2fed27a06
-- title:
--   DC contribution accumulation and matching: cm1FundingSurplus_mono_rate
-- statement:
--   Increasing the contribution rate cannot worsen the funding surplus when salary accumulation base is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c_1\le c_2\Rightarrow \Delta(c_1)\le\Delta(c_2)
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1FundingSurplus

namespace ActuarialValuation

theorem cm1FundingSurplus_mono_rate (salary revalue growth : ℕ → ℝ) (n : ℕ) (a annuity c₁ c₂ : ℝ) (hF : 0 ≤ cm1AccumulatedSalaryBase salary growth n) (hc : c₁ ≤ c₂) : cm1FundingSurplus salary revalue growth n a annuity c₁ ≤ cm1FundingSurplus salary revalue growth n a annuity c₂ := by sorry

end ActuarialValuation
