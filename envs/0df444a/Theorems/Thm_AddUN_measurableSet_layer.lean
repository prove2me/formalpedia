-- Prove2me | Theorems.Thm_AddUN_measurableSet_layer
-- name    : AddUN.measurableSet_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:32:53.481651+00:00
-- url     : https://prove2.me/theorems/01bd1942-0e34-4f48-87d2-b06cc63e0d14
-- title:
--   Add UN: measurable Set layer
-- statement:
--   The Add UN construction uses the measurable Set layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L90-L93
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L90-L93

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

theorem AddUN.measurableSet_layer (M : ℕ → ℕ) (k : ℕ) : MeasurableSet (layer U M k) := by sorry
