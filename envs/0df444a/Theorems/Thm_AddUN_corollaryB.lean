-- Prove2me | Theorems.Thm_AddUN_corollaryB
-- name    : AddUN.corollaryB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:43:55.532808+00:00
-- url     : https://prove2.me/theorems/e429e0e7-844f-41da-b4f9-f97d8c55a7b8
-- title:
--   Add UN: corollary B
-- statement:
--   **Corollary (b).** If `𝔠 ≤ ℵ₂`, then `add 𝒰𝒩 = add 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L55-L55
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L55-L55

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.corollaryB : CorollaryB := by sorry
