-- Prove2me | Theorems.Thm_Auto_aux_card_le_sharp_packing
-- name    : Auto.aux_card_le_sharp_packing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:09.48483+00:00
-- url     : https://prove2.me/theorems/513e362e-56df-4206-ac46-304c389eeba0
-- title:
--   Auto: aux card le sharp packing
-- statement:
--   The volume-packing estimate behind the sharp Euclidean radius comparison.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L537-L602
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L537-L602

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_card_le_sharp_packing {d : ℕ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s)
    (t : Finset (EuclideanSpace ℝ (Fin d)))
    (ht : ∀ c ∈ t, ‖c‖ ≤ s)
    (htsep : ∀ c ∈ t, ∀ e ∈ t, c ≠ e → r ≤ ‖c - e‖) :
    (t.card : ℝ) ≤ (3 * s / r) ^ d := by sorry
