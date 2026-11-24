-- Prove2me | Theorems.Thm_AddUN_measure_smallClopen_le
-- name    : AddUN.measure_smallClopen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:32:01.244135+00:00
-- url     : https://prove2.me/theorems/d4eb75b5-cf98-4556-a1ad-137e27fc5bfc
-- title:
--   Add UN: measure small Clopen le
-- statement:
--   The Add UN construction uses the measure small Clopen le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L68-L72
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L68-L72

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

theorem AddUN.measure_smallClopen_le (n k : ℕ) : cantorMeasure (smallClopen n k) ≤ 2⁻¹ ^ n := by sorry
