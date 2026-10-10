-- Prove2me | Theorems.Thm_ActuarialValuation_cm1AccumulatedSalaryBase_nonneg
-- name    : ActuarialValuation.cm1AccumulatedSalaryBase_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:53:42.426894+00:00
-- url     : https://prove2.me/theorems/c707e2e2-d242-477b-a744-ed9f6971cd3b
-- title:
--   DC contribution accumulation and matching: cm1AccumulatedSalaryBase_nonneg
-- statement:
--   Nonnegative pensionable salaries and growth factors yield nonnegative terminal contribution base. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_n\ge0
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase

namespace ActuarialValuation

theorem cm1AccumulatedSalaryBase_nonneg (salary growth : ℕ → ℝ) (n : ℕ) (hs : ∀ t ∈ Finset.range n, 0 ≤ salary t) (hg : ∀ t ∈ Finset.range n, 0 ≤ growth t) : 0 ≤ cm1AccumulatedSalaryBase salary growth n := by sorry

end ActuarialValuation
