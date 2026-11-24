-- Prove2me | Theorems.Thm_AddUN_theoremB_of_gotoCor513
-- name    : AddUN.theoremB_of_gotoCor513
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:28:09.183188+00:00
-- url     : https://prove2.me/theorems/290012f9-7b10-4af7-ab66-11ea78c9e91f
-- title:
--   Add UN: theorem B of goto Cor513
-- statement:
--   Theorem B follows from `add 𝒩 ≤ add 𝒰𝒩` (Goto, Corollary 5.13).
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L39-L40
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L39-L40

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.theoremB_of_gotoCor513 (hle : GotoCor513) : TheoremB := by sorry
