-- Prove2me | Theorems.Thm_AddUN_Coding_branch_succ_subset
-- name    : AddUN.Coding.branch_succ_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:10.54337+00:00
-- url     : https://prove2.me/theorems/b2abfd10-6691-4f3d-87f1-20ef0f5940bb
-- title:
--   Coding: branch succ subset
-- statement:
--   The Coding construction uses the branch succ subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L292-L297
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L292-L297

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

theorem AddUN.Coding.branch_succ_subset (m : ℕ) : branch K c f n₀ (m + 1) ⊆ branch K c f n₀ m := by sorry
