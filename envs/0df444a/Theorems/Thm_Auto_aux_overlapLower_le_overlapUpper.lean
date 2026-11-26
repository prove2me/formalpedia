-- Prove2me | Theorems.Thm_Auto_aux_overlapLower_le_overlapUpper
-- name    : Auto.aux_overlapLower_le_overlapUpper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:41.550795+00:00
-- url     : https://prove2.me/theorems/c658776b-a43e-4190-a81d-61c065244b36
-- title:
--   Auto: aux overlap Lower le overlap Upper
-- statement:
--   On the base cube, every common-overlap interval is nonempty.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L715-L732
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L715-L732

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

theorem Auto.aux_overlapLower_le_overlapUpper {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (u : aux_RVector n) (m : ℕ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ ε) (hεδ : ε ≤ δ) :
    aux_overlapLower hn ε u m ≤ aux_overlapUpper hn ε δ u m := by sorry
