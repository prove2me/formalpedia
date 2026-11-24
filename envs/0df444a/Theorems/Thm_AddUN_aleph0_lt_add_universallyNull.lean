-- Prove2me | Theorems.Thm_AddUN_aleph0_lt_add_universallyNull
-- name    : AddUN.aleph0_lt_add_universallyNull
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:29:44.4838+00:00
-- url     : https://prove2.me/theorems/3119a48b-6a1a-461e-be89-babbc740e29d
-- title:
--   Add UN: aleph0 lt add universally Null
-- statement:
--   `add 𝒰𝒩` is uncountable.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L106-L107
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L106-L107

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.aleph0_lt_add_universallyNull : ℵ₀ < add 𝒰𝒩 := by sorry
