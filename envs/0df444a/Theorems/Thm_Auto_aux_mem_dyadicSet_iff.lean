-- Prove2me | Theorems.Thm_Auto_aux_mem_dyadicSet_iff
-- name    : Auto.aux_mem_dyadicSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:21.320394+00:00
-- url     : https://prove2.me/theorems/6974c6ff-7b5c-492d-b422-4a959790a8c5
-- title:
--   Auto: aux mem dyadic Set iff
-- statement:
--   Characterize the occupied dyadic interval set.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L269-L279
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L269-L279

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_mem_dyadicSet_iff {J : ℕ} (t : Fin (J + 1) → ℝ)
    (ht : ∀ j, 0 < t j) (k : ℤ) :
    k ∈ aux_dyadicSet t ↔ ∃ j, (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1) := by sorry
