-- Prove2me | Theorems.Thm_AddUN_corollaries_of_theoremB
-- name    : AddUN.corollaries_of_theoremB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:16.09774+00:00
-- url     : https://prove2.me/theorems/f62dfb6f-ad92-4eb6-9dd5-23c5ea5bdc9d
-- title:
--   Add UN: corollaries of theorem B
-- statement:
--   All three corollaries follow from Theorem B and the two cited results.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L153-L157
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L153-L157

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.corollaries_of_theoremB (hB : TheoremB) (hG : Grzegorek) (hle : GotoCor513) :
    CorollaryA ∧ CorollaryB ∧ CorollaryC := by sorry
