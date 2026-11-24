-- Prove2me | Theorems.Thm_AddUN_iUnion_inner
-- name    : AddUN.iUnion_inner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:27:54.031271+00:00
-- url     : https://prove2.me/theorems/5660ca52-2cb9-4d1a-8e8f-2d646b5fce02
-- title:
--   Add UN: i Union inner
-- statement:
--   The Add UN construction uses the i Union inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L78-L83
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L78-L83

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}

theorem AddUN.iUnion_inner (hU : IsOpen U) : ⋃ n, inner U n = U := by sorry
