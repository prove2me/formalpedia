-- Prove2me | Theorems.Thm_Auto_aux_unitClosedBallVolume_eq_gamma
-- name    : Auto.aux_unitClosedBallVolume_eq_gamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:44.326051+00:00
-- url     : https://prove2.me/theorems/227b04ef-0196-4016-9fb6-a2e4d41217c3
-- title:
--   Auto: aux unit Closed Ball Volume eq gamma
-- statement:
--   Mathlib's Euclidean-ball formula identifies the unit-ball constant with the gamma-function
--   constant used in the draft (for positive dimension).
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1043-L1051
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1043-L1051

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_unitClosedBallVolume_eq_gamma {d : ℕ} (hd : 0 < d) :
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) =
      (Real.sqrt Real.pi) ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by sorry
