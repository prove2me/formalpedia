-- Prove2me | Theorems.Thm_AddUN_Coding_block_subset_low
-- name    : AddUN.Coding.block_subset_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:46.74547+00:00
-- url     : https://prove2.me/theorems/e1d7a2ce-9952-4a9a-85ee-a4021b2d8a08
-- title:
--   Coding: block subset low
-- statement:
--   The Coding construction uses the block subset low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L87-L90
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L87-L90

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

theorem AddUN.Coding.block_subset_low (n k : ℕ) : (block n k : Set ℕ) ⊆ low (n + 1) := by sorry
