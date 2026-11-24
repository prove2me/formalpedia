-- Prove2me | Theorems.Thm_AddUN_inner_mono
-- name    : AddUN.inner_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:27:24.847593+00:00
-- url     : https://prove2.me/theorems/9e9ea8c6-b753-4cba-adda-897c09434484
-- title:
--   Add UN: inner mono
-- statement:
--   The Add UN construction uses the inner mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L65-L66
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L65-L66

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

theorem AddUN.inner_mono {m n : ℕ} (h : m ≤ n) : inner U m ⊆ inner U n := by sorry
