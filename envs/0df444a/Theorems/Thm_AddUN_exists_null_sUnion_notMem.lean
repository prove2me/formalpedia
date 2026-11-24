-- Prove2me | Theorems.Thm_AddUN_exists_null_sUnion_notMem
-- name    : AddUN.exists_null_sUnion_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:07.780114+00:00
-- url     : https://prove2.me/theorems/14c2d35b-ee2a-4ef0-a3a4-de1dc81965f8
-- title:
--   Add UN: exists null s Union not Mem
-- statement:
--   Some family of null sets has a union that is not null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L145-L152
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L145-L152

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN

theorem AddUN.exists_null_sUnion_notMem : ∃ 𝒜 ⊆ 𝒩, ⋃₀ 𝒜 ∉ 𝒩 := by sorry
