-- Prove2me | Theorems.Thm_AddUN_Coding_apply_of_mem_hit
-- name    : AddUN.Coding.apply_of_mem_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:49.914515+00:00
-- url     : https://prove2.me/theorems/5a59ccb4-88b1-43c3-bfb7-992c30cfc587
-- title:
--   Coding: apply of mem hit
-- statement:
--   The Coding construction uses the apply of mem hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L141-L143
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L141-L143

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

theorem AddUN.Coding.apply_of_mem_hit {c : ℕ → Bool} {n k i : ℕ} {w : ℕ → Bool} (hw : w ∈ hit c n k)
    (hi : i < n) : w (coord n k (mu n + i)) = c i := by sorry
