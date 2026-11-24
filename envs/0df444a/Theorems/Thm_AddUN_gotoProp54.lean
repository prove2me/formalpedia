-- Prove2me | Theorems.Thm_AddUN_gotoProp54
-- name    : AddUN.gotoProp54
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:40:27.87059+00:00
-- url     : https://prove2.me/theorems/f8893f18-439d-4632-99d7-69332aa5d2ec
-- title:
--   Add UN: goto Prop54
-- statement:
--   **Goto, Proposition 5.4.** `non 𝒰𝒩 = non 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L299-L302
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean#L299-L302

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN

theorem AddUN.gotoProp54 : GotoProp54 := by sorry
