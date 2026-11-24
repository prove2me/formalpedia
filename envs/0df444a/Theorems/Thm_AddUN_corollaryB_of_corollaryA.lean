-- Prove2me | Theorems.Thm_AddUN_corollaryB_of_corollaryA
-- name    : AddUN.corollaryB_of_corollaryA
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:29:44.587627+00:00
-- url     : https://prove2.me/theorems/89c85bb2-39ec-4c2b-b50f-a079c21af9d8
-- title:
--   Add UN: corollary B of corollary A
-- statement:
--   Corollary (b) follows from Corollary (a) and `add 𝒩 ≤ add 𝒰𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L129-L138
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L129-L138

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.corollaryB_of_corollaryA (ha : CorollaryA) (hle : GotoCor513) : CorollaryB := by sorry
