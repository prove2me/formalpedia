-- Prove2me | Theorems.Thm_AddUN_exists_code_of_null
-- name    : AddUN.exists_code_of_null
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:32:04.271158+00:00
-- url     : https://prove2.me/theorems/ce33283b-dfb7-4a79-9093-76411f8f82fa
-- title:
--   Add UN: exists code of null
-- statement:
--   Every null set is contained in a section of the universal null set.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L108-L118
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L108-L118

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

theorem AddUN.exists_code_of_null {G : Set (ℕ → Bool)} (hG : cantorMeasure G = 0) :
    ∃ c : ℕ → ℕ, ∀ x ∈ G, (x, c) ∈ universalNull := by sorry
