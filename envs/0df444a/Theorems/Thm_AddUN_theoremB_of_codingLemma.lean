-- Prove2me | Theorems.Thm_AddUN_theoremB_of_codingLemma
-- name    : AddUN.theoremB_of_codingLemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:21.545733+00:00
-- url     : https://prove2.me/theorems/0cb922d2-904d-41be-8f58-92fdc0115d21
-- title:
--   Add UN: theorem B of coding Lemma
-- statement:
--   Theorem B follows from the coding lemma and `add 𝒩 ≤ add 𝒰𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremB.lean#L83-L85
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremB.lean#L83-L85

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_TheoremB
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.theoremB_of_codingLemma (hC : CodingLemma) (hle : GotoCor513) : TheoremB := by sorry
