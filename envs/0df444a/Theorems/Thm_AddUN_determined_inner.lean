-- Prove2me | Theorems.Thm_AddUN_determined_inner
-- name    : AddUN.determined_inner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:27:39.510792+00:00
-- url     : https://prove2.me/theorems/d06a4b22-a207-4c42-8f1c-1e194dcbc20e
-- title:
--   Add UN: determined inner
-- statement:
--   The Add UN construction uses the determined inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L68-L69
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L68-L69

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

theorem AddUN.determined_inner (n : ℕ) : Determined (↑(Finset.range n)) (inner U n) := by sorry
