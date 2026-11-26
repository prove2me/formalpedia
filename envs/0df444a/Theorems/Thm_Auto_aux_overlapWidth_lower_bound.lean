-- Prove2me | Theorems.Thm_Auto_aux_overlapWidth_lower_bound
-- name    : Auto.aux_overlapWidth_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:00.743275+00:00
-- url     : https://prove2.me/theorems/ebca237d-86a1-4279-98c4-8e2ca20b163f
-- title:
--   Auto: aux overlap Width lower bound
-- statement:
--   On the base cube, the common overlap width is at least `δ - ε`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L779-L795
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L779-L795

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_overlapWidth_lower_bound {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (u : aux_RVector n) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ ε) :
    δ - ε ≤ aux_overlapWidth hn ε δ u := by sorry
