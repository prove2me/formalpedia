-- Prove2me | Theorems.Thm_AddUN_Coding_finite_bad
-- name    : AddUN.Coding.finite_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:11.813297+00:00
-- url     : https://prove2.me/theorems/30a49484-bb0b-4366-aae2-b3e0c5ae7d6a
-- title:
--   Coding: finite bad
-- statement:
--   The Coding construction uses the finite bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L260-L265
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L260-L265

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

theorem AddUN.Coding.finite_bad {K : Set (ℕ → Bool)} (hK : MeasurableSet K) (c : ℕ → Bool) (n : ℕ) :
    (bad K c n).Finite := by sorry
