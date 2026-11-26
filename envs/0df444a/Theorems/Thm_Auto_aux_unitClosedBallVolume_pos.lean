-- Prove2me | Theorems.Thm_Auto_aux_unitClosedBallVolume_pos
-- name    : Auto.aux_unitClosedBallVolume_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:22.8731+00:00
-- url     : https://prove2.me/theorems/104317db-a4d2-56dc-a75a-2ee35d039ee6
-- title:
--   Auto: aux unit Closed Ball Volume pos
-- statement:
--   The unit-ball volume is strictly positive.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1034-L1037
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1034-L1037

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_unitClosedBallVolume_pos {d : ℕ} :
    0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by sorry
