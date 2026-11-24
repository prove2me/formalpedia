-- Prove2me | Theorems.Thm_AddUN_grzegorek
-- name    : AddUN.grzegorek
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:57.664405+00:00
-- url     : https://prove2.me/theorems/cc1520a0-94c0-4165-8806-2d1bf0d038dc
-- title:
--   Add UN: grzegorek
-- statement:
--   **Grzegorek's theorem.** There is a universally null set of cardinality `non 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L123-L187
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L123-L187

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

theorem AddUN.grzegorek : Grzegorek := by sorry
