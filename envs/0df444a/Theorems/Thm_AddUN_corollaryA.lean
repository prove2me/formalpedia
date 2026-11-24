-- Prove2me | Theorems.Thm_AddUN_corollaryA
-- name    : AddUN.corollaryA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:43:55.6709+00:00
-- url     : https://prove2.me/theorems/730b7172-97f3-4600-9bd9-5426bd95a305
-- title:
--   Add UN: corollary A
-- statement:
--   **Corollary (a).** If `non 𝒩 = cof 𝒩`, then `add 𝒰𝒩 = add 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L52-L52
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L52-L52

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.corollaryA : CorollaryA := by sorry
