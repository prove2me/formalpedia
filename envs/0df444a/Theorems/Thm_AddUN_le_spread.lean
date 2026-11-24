-- Prove2me | Theorems.Thm_AddUN_le_spread
-- name    : AddUN.le_spread
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:33:38.885912+00:00
-- url     : https://prove2.me/theorems/dcd70cd3-2de9-472f-893f-a1ac283045cf
-- title:
--   Add UN: le spread
-- statement:
--   The Add UN construction uses the le spread property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L215-L215
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L215-L215

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

theorem AddUN.le_spread (g : ℕ → ℕ) (k₀ k : ℕ) : g (k + k₀) ≤ spread g k₀ k := by sorry
