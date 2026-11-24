-- Prove2me | Theorems.Thm_AddUN_isOpen_inner
-- name    : AddUN.isOpen_inner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:27:44.4339+00:00
-- url     : https://prove2.me/theorems/ac967eaf-7415-4fcc-91bd-2cdcbb9fc417
-- title:
--   Add UN: is Open inner
-- statement:
--   The Add UN construction uses the is Open inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L71-L76
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L71-L76

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}

theorem AddUN.isOpen_inner (n : ℕ) : IsOpen (inner U n) := by sorry
