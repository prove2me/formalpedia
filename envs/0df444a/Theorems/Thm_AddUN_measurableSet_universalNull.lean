-- Prove2me | Theorems.Thm_AddUN_measurableSet_universalNull
-- name    : AddUN.measurableSet_universalNull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:32:02.95867+00:00
-- url     : https://prove2.me/theorems/8247e30c-7470-49e7-a5f9-c071724deac8
-- title:
--   Add UN: measurable Set universal Null
-- statement:
--   The Add UN construction uses the measurable Set universal Null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L79-L95
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L79-L95

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

theorem AddUN.measurableSet_universalNull : MeasurableSet universalNull := by sorry
