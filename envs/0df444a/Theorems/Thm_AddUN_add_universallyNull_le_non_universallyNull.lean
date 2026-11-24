-- Prove2me | Theorems.Thm_AddUN_add_universallyNull_le_non_universallyNull
-- name    : AddUN.add_universallyNull_le_non_universallyNull
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:29:49.895376+00:00
-- url     : https://prove2.me/theorems/fa4dd2cf-7783-4ef6-b01e-59037961d2c2
-- title:
--   Add UN: add universally Null le non universally Null
-- statement:
--   `add 𝒰𝒩 ≤ non 𝒰𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L110-L112
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L110-L112

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.add_universallyNull_le_non_universallyNull : add 𝒰𝒩 ≤ non 𝒰𝒩 := by sorry
