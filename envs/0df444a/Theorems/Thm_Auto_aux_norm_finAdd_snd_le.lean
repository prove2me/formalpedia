-- Prove2me | Theorems.Thm_Auto_aux_norm_finAdd_snd_le
-- name    : Auto.aux_norm_finAdd_snd_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:28.397146+00:00
-- url     : https://prove2.me/theorems/21675fd2-7f5f-4e3b-a754-fb6930fe26f7
-- title:
--   Auto: aux norm fin Add snd le
-- statement:
--   Each coordinate block has norm at most the norm of the whole Euclidean vector.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2406-L2423
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2406-L2423

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_norm_finAdd_snd_le {n m : ℕ} (w : EuclideanSpace ℝ (Fin (n + m))) :
    ‖(EuclideanSpace.finAddEquivProd w).2‖ ≤ ‖w‖ := by sorry
