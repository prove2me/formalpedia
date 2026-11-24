-- Prove2me | Theorems.Thm_AddUN_corollaryA_of_theoremB
-- name    : AddUN.corollaryA_of_theoremB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:29:45.288989+00:00
-- url     : https://prove2.me/theorems/a7acd808-667e-4bd4-a704-595ac9764334
-- title:
--   Add UN: corollary A of theorem B
-- statement:
--   Corollary (a) follows from Theorem B and Grzegorek's theorem.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L123-L126
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L123-L126

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.corollaryA_of_theoremB (hB : TheoremB) (hG : Grzegorek) : CorollaryA := by sorry
