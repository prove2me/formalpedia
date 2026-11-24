-- Prove2me | Theorems.Thm_AddUN_add_universallyNull_le_min
-- name    : AddUN.add_universallyNull_le_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:44:23.698996+00:00
-- url     : https://prove2.me/theorems/1dfe8a70-9775-4e55-945c-c49ad338326a
-- title:
--   Add UN: add universally Null le min
-- statement:
--   `add 𝒩 ≤ add 𝒰𝒩 ≤ min 𝔡 (non 𝒩)`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L68-L69
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L68-L69

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.add_universallyNull_le_min : add 𝒰𝒩 ≤ min dominatingNumber (non 𝒩) := by sorry
