-- Prove2me | Theorems.Thm_AddUN_theoremB
-- name    : AddUN.theoremB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:34:23.83321+00:00
-- url     : https://prove2.me/theorems/187a5409-110a-4525-9010-9ba748486eaa
-- title:
--   Add UN: theorem B
-- statement:
--   **Theorem B.** If there is a universally null set of cardinality `cof 𝒩`, then
--   `add 𝒰𝒩 = add 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L49-L49
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Main.lean#L49-L49

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN

theorem AddUN.theoremB : TheoremB := by sorry
