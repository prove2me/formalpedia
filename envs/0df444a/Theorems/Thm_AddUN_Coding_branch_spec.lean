-- Prove2me | Theorems.Thm_AddUN_Coding_branch_spec
-- name    : AddUN.Coding.branch_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:11.45091+00:00
-- url     : https://prove2.me/theorems/380a5587-24b3-49db-8f8f-5665f8847894
-- title:
--   Coding: branch spec
-- statement:
--   The invariant of the fusion: the events of the branch are closed, depend only on the blocks
--   of lower stages, and meet `K` in a set of measure at least `theta`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L301-L335
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L301-L335

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
variable {K : Set (ℕ → Bool)} {c : ℕ → Bool} {f : ℕ → ℕ} {n₀ : ℕ}

theorem AddUN.Coding.branch_spec (hn₀ : theta n₀ ≤ cantorMeasure.real K) (m : ℕ) :
    IsClosed (branch K c f n₀ m) ∧ Determined (low (n₀ + m)) (branch K c f n₀ m) ∧
      theta (n₀ + m) ≤ cantorMeasure.real (K ∩ branch K c f n₀ m) := by sorry
