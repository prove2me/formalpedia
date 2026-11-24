-- Prove2me | Theorems.Thm_AddUN_Coding_card_le_of_subset_bad
-- name    : AddUN.Coding.card_le_of_subset_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:25:10.921799+00:00
-- url     : https://prove2.me/theorems/c328671d-e19f-4e91-8038-31097f7e4362
-- title:
--   Coding: card le of subset bad
-- statement:
--   The width of the slalom.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L229-L258
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L229-L258

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

theorem AddUN.Coding.card_le_of_subset_bad {K : Set (ℕ → Bool)} (hK : MeasurableSet K) {c : ℕ → Bool} {n : ℕ}
    (J : Finset ℕ) (hJ : (J : Set ℕ) ⊆ bad K c n) : J.card ≤ 2 ^ (3 * mu n + n) := by sorry
