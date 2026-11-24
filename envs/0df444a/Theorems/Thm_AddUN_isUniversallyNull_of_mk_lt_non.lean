-- Prove2me | Theorems.Thm_AddUN_isUniversallyNull_of_mk_lt_non
-- name    : AddUN.isUniversallyNull_of_mk_lt_non
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:26:31.209194+00:00
-- url     : https://prove2.me/theorems/72f3d3ea-a87f-4529-94ff-2ed1d928def0
-- title:
--   Add UN: is Universally Null of mk lt non
-- statement:
--   A set of cardinality less than `non 𝒩` is universally null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L288-L296
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L288-L296

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN

theorem AddUN.isUniversallyNull_of_mk_lt_non {A : Set (ℕ → Bool)} (hA : #A < non 𝒩) :
    IsUniversallyNull A := by sorry
