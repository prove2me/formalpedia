-- Prove2me | Theorems.Thm_ActuarialValuation_cm1FundingSurplus_zero_rate
-- name    : ActuarialValuation.cm1FundingSurplus_zero_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:55:56.44178+00:00
-- url     : https://prove2.me/theorems/15d04923-6ca4-480b-afd4-8558f5f23c81
-- title:
--   DC contribution accumulation and matching: cm1FundingSurplus_zero_rate
-- statement:
--   With no employer or member contributions, the actuarial shortfall equals the promised CARE benefit liability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta(0)=-L
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability
import Definitions.Def_actuarial_cm1FundingSurplus

namespace ActuarialValuation

theorem cm1FundingSurplus_zero_rate (salary revalue growth : ℕ → ℝ) (n : ℕ) (a annuity : ℝ) : cm1FundingSurplus salary revalue growth n a annuity 0 = - cm1CARELiability salary revalue n a annuity := by sorry

end ActuarialValuation
