-- Prove2me | Theorems.Thm_Auto_aux_commonOverlapSet_subset_scale
-- name    : Auto.aux_commonOverlapSet_subset_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:30.717266+00:00
-- url     : https://prove2.me/theorems/e3c06fbb-29b2-4b26-ba20-500945840881
-- title:
--   Auto: aux common Overlap Set subset scale
-- statement:
--   Every overlap indexed by `range N` lies inside the scale interval
--   `[0,N)`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L801-L817
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L801-L817

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

theorem Auto.aux_commonOverlapSet_subset_scale {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (hwidth : ε + δ < 1) (u : aux_RVector n)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) (N : ℕ) (q : Fin N) :
    aux_commonOverlapSet ε δ u q.val ⊆ Ico (0 : ℝ) N := by sorry
