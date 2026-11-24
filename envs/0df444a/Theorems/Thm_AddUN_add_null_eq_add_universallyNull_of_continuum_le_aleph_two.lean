-- Prove2me | Theorems.Thm_AddUN_add_null_eq_add_universallyNull_of_continuum_le_aleph_two
-- name    : AddUN.add_null_eq_add_universallyNull_of_continuum_le_aleph_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:44:28.216522+00:00
-- url     : https://prove2.me/theorems/45ae84f3-a9d4-44c5-b372-4adc3a27e48b
-- title:
--   Add UN: add null eq add universally Null of continuum le aleph two
-- statement:
--   If `𝔠 ≤ ℵ₂`, then `add 𝒩 = add 𝒰𝒩`: the open question `Question63` has a positive answer
--   in every model with `𝔠 ≤ ℵ₂`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L63-L65
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L63-L65

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.add_null_eq_add_universallyNull_of_continuum_le_aleph_two
    (h : (𝔠 : Cardinal.{0}) ≤ ℵ_ 2) : add 𝒩 = add 𝒰𝒩 := by sorry
