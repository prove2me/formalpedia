-- Prove2me | Theorems.Thm_AddUN_exists_clopens_iUnion_eq
-- name    : AddUN.exists_clopens_iUnion_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:30:04.63891+00:00
-- url     : https://prove2.me/theorems/f81fde10-2db8-4726-96fd-8a5c9978c620
-- title:
--   Add UN: exists clopens i Union eq
-- statement:
--   Every open subset of the Cantor space is the union of a sequence of pairwise disjoint clopen
--   sets. The measures of these sets add up to the measure of the open set.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L50-L73
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean#L50-L73

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

theorem AddUN.exists_clopens_iUnion_eq (μ : Measure (ℕ → Bool)) {U : Set (ℕ → Bool)} (hU : IsOpen U) :
    ∃ D : ℕ → Clopens (ℕ → Bool), ⋃ r, (D r : Set (ℕ → Bool)) = U ∧ ∑' r, μ (D r) = μ U := by sorry
