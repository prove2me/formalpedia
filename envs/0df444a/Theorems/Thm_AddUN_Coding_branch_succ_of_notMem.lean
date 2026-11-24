-- Prove2me | Theorems.Thm_AddUN_Coding_branch_succ_of_notMem
-- name    : AddUN.Coding.branch_succ_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:54.171798+00:00
-- url     : https://prove2.me/theorems/eba856e7-ea64-45a1-8383-69815b6052a8
-- title:
--   Coding: branch succ of not Mem
-- statement:
--   The Coding construction uses the branch succ of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L288-L290
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L288-L290

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

theorem AddUN.Coding.branch_succ_of_notMem {m : ℕ} (h : f (n₀ + m) ∉ bad K c (n₀ + m)) :
    branch K c f n₀ (m + 1) = branch K c f n₀ m ∩ hit c (n₀ + m) (f (n₀ + m)) := by sorry
