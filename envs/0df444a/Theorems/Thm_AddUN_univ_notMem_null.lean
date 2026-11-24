-- Prove2me | Theorems.Thm_AddUN_univ_notMem_null
-- name    : AddUN.univ_notMem_null
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:09.911103+00:00
-- url     : https://prove2.me/theorems/f0099926-8be3-42f4-9d0a-a1533dd81bb3
-- title:
--   Add UN: univ not Mem null
-- statement:
--   The Cantor space is not null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L98-L99
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L98-L99

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.univ_notMem_null : Set.univ ∉ 𝒩 := by sorry
