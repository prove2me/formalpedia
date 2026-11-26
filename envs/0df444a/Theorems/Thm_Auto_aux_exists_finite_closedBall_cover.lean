-- Prove2me | Theorems.Thm_Auto_aux_exists_finite_closedBall_cover
-- name    : Auto.aux_exists_finite_closedBall_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:40.135861+00:00
-- url     : https://prove2.me/theorems/416ba4e1-8d06-46ca-91eb-60be37ce7c4a
-- title:
--   Auto: aux exists finite closed Ball cover
-- statement:
--   Every closed ball in a proper normed space has a finite cover by closed balls of any positive
--   radius.  This is the compactness input for radius-independence of `W₀`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L523-L534
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L523-L534

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_exists_finite_closedBall_cover {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (r : ℝ) (hr : 0 < r) (s : ℝ) :
    ∃ t : Finset E, ∀ y ∈ closedBall (0 : E) s, ∃ z ∈ t, y ∈ closedBall z r := by sorry
