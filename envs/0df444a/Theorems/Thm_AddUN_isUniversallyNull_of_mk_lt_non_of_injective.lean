-- Prove2me | Theorems.Thm_AddUN_isUniversallyNull_of_mk_lt_non_of_injective
-- name    : AddUN.isUniversallyNull_of_mk_lt_non_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:53.844517+00:00
-- url     : https://prove2.me/theorems/e17d32e3-4591-48d4-a9fc-26a2343510d1
-- title:
--   Add UN: is Universally Null of mk lt non of injective
-- statement:
--   A set of cardinality less than `non 𝒩` is universally null, in every measurable space that
--   has a measurable injection into the Cantor space.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L43-L46
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean#L43-L46

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

theorem AddUN.isUniversallyNull_of_mk_lt_non_of_injective {Z : Type} [MeasurableSpace Z]
    {j : Z → ℕ → Bool} (hj : Measurable j) (hinj : Function.Injective j) {A : Set Z}
    (hA : #A < non 𝒩) : IsUniversallyNull A := by sorry
