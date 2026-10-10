-- Prove2me | Theorems.Thm_ActuarialValuation_cm1DCFund_zero_rate
-- name    : ActuarialValuation.cm1DCFund_zero_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:53:59.295372+00:00
-- url     : https://prove2.me/theorems/72fe97a9-76a4-4483-9b43-7ce9a42c6869
-- title:
--   DC contribution accumulation and matching: cm1DCFund_zero_rate
-- statement:
--   Without contributions a salary-linked DC fund does not accumulate principal in this model. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c=0\Rightarrow A_n=0
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DCFund

namespace ActuarialValuation

theorem cm1DCFund_zero_rate (salary growth : ℕ → ℝ) (n : ℕ) : cm1DCFund salary growth n 0 = 0 := by sorry

end ActuarialValuation
