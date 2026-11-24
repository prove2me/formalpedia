-- Prove2me | Theorems.Thm_AddUN_determined_layer
-- name    : AddUN.determined_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:33:25.21618+00:00
-- url     : https://prove2.me/theorems/5185958b-879b-475b-baa3-6a3f5d16800b
-- title:
--   Add UN: determined layer
-- statement:
--   The Add UN construction uses the determined layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L95-L101
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L95-L101

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

theorem AddUN.determined_layer {M : ℕ → ℕ} (hM : Monotone M) (k : ℕ) :
    Determined (↑(Finset.range (M k))) (layer U M k) := by sorry
