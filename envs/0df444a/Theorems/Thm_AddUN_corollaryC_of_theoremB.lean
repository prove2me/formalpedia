-- Prove2me | Theorems.Thm_AddUN_corollaryC_of_theoremB
-- name    : AddUN.corollaryC_of_theoremB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:29:48.074956+00:00
-- url     : https://prove2.me/theorems/1d526302-ad9f-4f8a-9fc6-ba540e108806
-- title:
--   Add UN: corollary C of theorem B
-- statement:
--   Corollary (c) follows from Theorem B and Corollaries (a) and (b).
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L141-L150
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L141-L150

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.corollaryC_of_theoremB (hB : TheoremB) (ha : CorollaryA) (hb : CorollaryB) :
    CorollaryC := by sorry
