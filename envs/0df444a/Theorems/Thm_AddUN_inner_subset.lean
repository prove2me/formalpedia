-- Prove2me | Theorems.Thm_AddUN_inner_subset
-- name    : AddUN.inner_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:26:54.217708+00:00
-- url     : https://prove2.me/theorems/f9fa9c8d-9203-45f9-af7e-d266a0981ae2
-- title:
--   Add UN: inner subset
-- statement:
--   The Add UN construction uses the inner subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L63-L63
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L63-L63

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

theorem AddUN.inner_subset (n : ℕ) : inner U n ⊆ U := by sorry
