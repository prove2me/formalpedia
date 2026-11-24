-- Prove2me | Theorems.Thm_AddUN_Coding_mem_marker
-- name    : AddUN.Coding.mem_marker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:36.323932+00:00
-- url     : https://prove2.me/theorems/889a4cc9-564f-435f-ad9e-2f319db9b73b
-- title:
--   Coding: mem marker
-- statement:
--   The Coding construction uses the mem marker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L127-L129
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L127-L129

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

theorem AddUN.Coding.mem_marker {n k : ℕ} {w : ℕ → Bool} :
    w ∈ marker n k ↔ ∀ j < mu n, w (coord n k j) = false := by sorry
