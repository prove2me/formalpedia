-- Prove2me | Theorems.Thm_AddUN_add_universallyNull_le_add_null_of_codingLemma
-- name    : AddUN.add_universallyNull_le_add_null_of_codingLemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:34.618812+00:00
-- url     : https://prove2.me/theorems/91e2c58a-7e09-423f-b830-353cfcb9cffa
-- title:
--   Add UN: add universally Null le add null of coding Lemma
-- statement:
--   The hard direction of Theorem B, from the coding lemma: if there is a universally null set
--   of cardinality `cof 𝒩`, then `add 𝒰𝒩 ≤ add 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremB.lean#L48-L80
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremB.lean#L48-L80

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_TheoremB
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.add_universallyNull_le_add_null_of_codingLemma (hC : CodingLemma)
    (A : Set (ℕ → Bool)) (hA : IsUniversallyNull A) (hcard : #A = cof 𝒩) :
    add 𝒰𝒩 ≤ add 𝒩 := by sorry
