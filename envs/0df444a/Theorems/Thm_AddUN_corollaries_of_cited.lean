-- Prove2me | Theorems.Thm_AddUN_corollaries_of_cited
-- name    : AddUN.corollaries_of_cited
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:26:47.925937+00:00
-- url     : https://prove2.me/theorems/ebf06609-6e22-4758-b4cd-e5fce542af14
-- title:
--   Add UN: corollaries of cited
-- statement:
--   Corollaries (a), (b) and (c) follow from Grzegorek's theorem and `add 𝒩 ≤ add 𝒰𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L43-L45
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L43-L45

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.corollaries_of_cited (hG : Grzegorek) (hle : GotoCor513) :
    CorollaryA ∧ CorollaryB ∧ CorollaryC := by sorry
