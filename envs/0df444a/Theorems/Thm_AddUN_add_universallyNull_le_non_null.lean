-- Prove2me | Theorems.Thm_AddUN_add_universallyNull_le_non_null
-- name    : AddUN.add_universallyNull_le_non_null
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:14.257808+00:00
-- url     : https://prove2.me/theorems/e641b857-3571-4458-bfbe-6bedb662b9ae
-- title:
--   Add UN: add universally Null le non null
-- statement:
--   `add 𝒰𝒩 ≤ non 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L119-L120
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L119-L120

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.add_universallyNull_le_non_null : add 𝒰𝒩 ≤ non 𝒩 := by sorry
