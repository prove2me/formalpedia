-- Prove2me | Theorems.Thm_AddUN_measure_section_universalNull
-- name    : AddUN.measure_section_universalNull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:32:10.454257+00:00
-- url     : https://prove2.me/theorems/93c67e25-4317-4365-95d8-71adb257509c
-- title:
--   Add UN: measure section universal Null
-- statement:
--   The Add UN construction uses the measure section universal Null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L97-L105
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L97-L105

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN

theorem AddUN.measure_section_universalNull (c : ℕ → ℕ) :
    cantorMeasure {x | (x, c) ∈ universalNull} = 0 := by sorry
