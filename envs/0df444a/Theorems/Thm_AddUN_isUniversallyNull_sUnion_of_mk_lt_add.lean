-- Prove2me | Theorems.Thm_AddUN_isUniversallyNull_sUnion_of_mk_lt_add
-- name    : AddUN.isUniversallyNull_sUnion_of_mk_lt_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:31:22.784484+00:00
-- url     : https://prove2.me/theorems/40dca26f-53c0-4b23-bd04-b351cfc87912
-- title:
--   Add UN: is Universally Null s Union of mk lt add
-- statement:
--   A union of fewer than `add 𝒩` universally null sets is universally null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Additivity.lean#L78-L80
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Additivity.lean#L78-L80

module
public import Definitions.Def_AddUN_Coding
public import Definitions.Def_AddUN_Additivity
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
open Coding

theorem AddUN.isUniversallyNull_sUnion_of_mk_lt_add {𝒜 : Set (Set (ℕ → Bool))}
    (h𝒜 : ∀ A ∈ 𝒜, IsUniversallyNull A) (hcard : #𝒜 < add 𝒩) : IsUniversallyNull (⋃₀ 𝒜) := by sorry
