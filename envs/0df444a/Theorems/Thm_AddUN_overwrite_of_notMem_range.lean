-- Prove2me | Theorems.Thm_AddUN_overwrite_of_notMem_range
-- name    : AddUN.overwrite_of_notMem_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:33:33.621657+00:00
-- url     : https://prove2.me/theorems/489c4a81-c806-4698-80f0-6d9760230a3e
-- title:
--   Add UN: overwrite of not Mem range
-- statement:
--   The Add UN construction uses the overwrite of not Mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L225-L228
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L225-L228

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

theorem AddUN.overwrite_of_notMem_range {h : ℕ → ℕ} (c u : ℕ → Bool) {i : ℕ} (hi : i ∉ range h) :
    overwrite h c u i = u i := by sorry
