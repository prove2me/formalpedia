-- Prove2me | Theorems.Thm_Auto_aux_norm_finAdd_le
-- name    : Auto.aux_norm_finAdd_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:26.574371+00:00
-- url     : https://prove2.me/theorems/8530257e-bc52-5c9e-83f8-61ef6d9e3bca
-- title:
--   Auto: aux norm fin Add le
-- statement:
--   The coordinate splitting does not increase norm.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2426-L2429
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2426-L2429

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_norm_finAdd_le {n m : ℕ} (w : EuclideanSpace ℝ (Fin (n + m))) :
    ‖EuclideanSpace.finAddEquivProd w‖ ≤ ‖w‖ := by sorry
