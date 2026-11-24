-- Prove2me | Theorems.Thm_AddUN_add_universallyNull_le_add_null
-- name    : AddUN.add_universallyNull_le_add_null
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:44:02.928829+00:00
-- url     : https://prove2.me/theorems/5cb0b3b2-cbe5-4fec-905d-5ebc3a15ed4e
-- title:
--   Add UN: add universally Null le add null
-- statement:
--   **The hard direction of Theorem B.** If there is a universally null set of cardinality
--   `cof 𝒩`, then `add 𝒰𝒩 ≤ add 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L34-L36
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L34-L36

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.add_universallyNull_le_add_null (A : Set (ℕ → Bool)) (hA : IsUniversallyNull A)
    (hcard : #A = cof 𝒩) : add 𝒰𝒩 ≤ add 𝒩 := by sorry
