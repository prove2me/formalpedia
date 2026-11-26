-- Prove2me | Theorems.Thm_Auto_aux_norm_finAdd_fst_le
-- name    : Auto.aux_norm_finAdd_fst_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:17.355331+00:00
-- url     : https://prove2.me/theorems/e78ac97d-457a-4346-9f4b-390fa72549eb
-- title:
--   Auto: aux norm fin Add fst le
-- statement:
--   Each coordinate block has norm at most the norm of the whole Euclidean vector.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2386-L2403
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2386-L2403

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_norm_finAdd_fst_le {n m : ℕ} (w : EuclideanSpace ℝ (Fin (n + m))) :
    ‖(EuclideanSpace.finAddEquivProd w).1‖ ≤ ‖w‖ := by sorry
