-- Prove2me | Theorems.Thm_AddUN_aleph0_lt_add_null
-- name    : AddUN.aleph0_lt_add_null
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:24:00.379905+00:00
-- url     : https://prove2.me/theorems/c9d088d3-5970-46aa-8589-61e4603bdac2
-- title:
--   Add UN: aleph0 lt add null
-- statement:
--   `add 𝒩` is uncountable.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L102-L103
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L102-L103

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.aleph0_lt_add_null : ℵ₀ < add 𝒩 := by sorry
