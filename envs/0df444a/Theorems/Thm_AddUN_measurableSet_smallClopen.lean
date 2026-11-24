-- Prove2me | Theorems.Thm_AddUN_measurableSet_smallClopen
-- name    : AddUN.measurableSet_smallClopen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:32:10.983121+00:00
-- url     : https://prove2.me/theorems/9d8a6f01-c451-4d10-8173-5930187ae32f
-- title:
--   Add UN: measurable Set small Clopen
-- statement:
--   The Add UN construction uses the measurable Set small Clopen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L62-L66
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L62-L66

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

theorem AddUN.measurableSet_smallClopen (n k : ℕ) : MeasurableSet (smallClopen n k) := by sorry
