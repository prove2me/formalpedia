-- Prove2me | Theorems.Thm_Auto_aux_overlapWidth_invariant
-- name    : Auto.aux_overlapWidth_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:48.679587+00:00
-- url     : https://prove2.me/theorems/37de5c97-bf6d-4c72-9a1e-1a3537aabd1c
-- title:
--   Auto: aux overlap Width invariant
-- statement:
--   The length of a common overlap interval is independent of its lattice
--   time.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L758-L764
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L758-L764

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

theorem Auto.aux_overlapWidth_invariant {n : ℕ} (hn : 0 < n)
    (ε δ : ℝ) (u : aux_RVector n) (m : ℕ) :
    aux_overlapUpper hn ε δ u m - aux_overlapLower hn ε u m =
      aux_overlapUpper hn ε δ u 0 - aux_overlapLower hn ε u 0 := by sorry
