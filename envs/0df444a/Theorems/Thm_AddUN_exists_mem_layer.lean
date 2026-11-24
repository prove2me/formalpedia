-- Prove2me | Theorems.Thm_AddUN_exists_mem_layer
-- name    : AddUN.exists_mem_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:33:20.217414+00:00
-- url     : https://prove2.me/theorems/be84c90f-c197-4194-b831-f18d9ae6fc1c
-- title:
--   Add UN: exists mem layer
-- statement:
--   The Add UN construction uses the exists mem layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L103-L115
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L103-L115

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

theorem AddUN.exists_mem_layer (hU : IsOpen U) {M : ℕ → ℕ} (hM : StrictMono M) {y : ℕ → Bool}
    (hy : y ∈ U) : ∃ k, y ∈ layer U M k := by sorry
