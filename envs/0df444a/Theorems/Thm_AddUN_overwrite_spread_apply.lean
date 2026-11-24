-- Prove2me | Theorems.Thm_AddUN_overwrite_spread_apply
-- name    : AddUN.overwrite_spread_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:33:31.859346+00:00
-- url     : https://prove2.me/theorems/ed9c346f-596b-4582-9dfc-f7d5ddd296cc
-- title:
--   Add UN: overwrite spread apply
-- statement:
--   The Add UN construction uses the overwrite spread apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L221-L223
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean#L221-L223

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

theorem AddUN.overwrite_spread_apply (g : ℕ → ℕ) (k₀ : ℕ) (c u : ℕ → Bool) (n : ℕ) :
    overwrite (spread g k₀) c u (spread g k₀ n) = c n := by sorry
