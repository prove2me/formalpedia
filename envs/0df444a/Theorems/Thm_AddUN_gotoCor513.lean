-- Prove2me | Theorems.Thm_AddUN_gotoCor513
-- name    : AddUN.gotoCor513
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:14.198817+00:00
-- url     : https://prove2.me/theorems/2ccfd29e-3225-4133-a935-065d20b51b7b
-- title:
--   Add UN: goto Cor513
-- statement:
--   **Goto, Corollary 5.13.** `add 𝒩 ≤ add 𝒰𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Additivity.lean#L83-L94
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Additivity.lean#L83-L94

module
public import Definitions.Def_AddUN_Coding
public import Definitions.Def_AddUN_Additivity
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
open Coding

theorem AddUN.gotoCor513 : GotoCor513 := by sorry
