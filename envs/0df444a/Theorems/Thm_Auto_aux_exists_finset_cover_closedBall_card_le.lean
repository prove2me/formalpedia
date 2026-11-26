-- Prove2me | Theorems.Thm_Auto_aux_exists_finset_cover_closedBall_card_le
-- name    : Auto.aux_exists_finset_cover_closedBall_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:03.93654+00:00
-- url     : https://prove2.me/theorems/96e5a01c-ba14-50f2-a918-088b5c0f2f76
-- title:
--   Auto: aux exists finset cover closed Ball card le
-- statement:
--   A closed Euclidean ball has a finite `r`-cover with the sharp packing count from the draft.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L605-L653
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L605-L653

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_exists_finset_cover_closedBall_card_le {d : ℕ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)),
      ((closedBall (0 : EuclideanSpace ℝ (Fin d)) s : Set _) ⊆
        ⋃ c ∈ t, closedBall c r) ∧
      (t.card : ℝ) ≤ (3 * s / r) ^ d := by sorry
