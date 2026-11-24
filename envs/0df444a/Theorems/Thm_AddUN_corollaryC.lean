-- Prove2me | Theorems.Thm_AddUN_corollaryC
-- name    : AddUN.corollaryC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:44:16.417808+00:00
-- url     : https://prove2.me/theorems/e194987f-5fd4-4bd9-af75-f78d501d0cc3
-- title:
--   Add UN: corollary C
-- statement:
--   **Corollary (c).** If `add 𝒩 < add 𝒰𝒩`, then `ℵ₃ ≤ 𝔠`, `non 𝒩 < cof 𝒩`, and every
--   universally null set has cardinality less than `cof 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L59-L59
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L59-L59

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.corollaryC : CorollaryC := by sorry
