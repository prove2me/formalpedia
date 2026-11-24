-- Prove2me | Theorems.Thm_AddUN_Coding_mem_hit
-- name    : AddUN.Coding.mem_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:45.072936+00:00
-- url     : https://prove2.me/theorems/7842e7b0-f1c4-47fc-87ca-7dac26322728
-- title:
--   Coding: mem hit
-- statement:
--   The Coding construction uses the mem hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L131-L133
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L131-L133

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

theorem AddUN.Coding.mem_hit {c : ℕ → Bool} {n k : ℕ} {w : ℕ → Bool} :
    w ∈ hit c n k ↔ ∀ j < mu n + n, w (coord n k j) = pattern c (coord n k j) := by sorry
