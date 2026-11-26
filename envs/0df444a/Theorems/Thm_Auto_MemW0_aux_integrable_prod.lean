-- Prove2me | Theorems.Thm_Auto_MemW0_aux_integrable_prod
-- name    : Auto.MemW0.aux_integrable_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:52:37.998197+00:00
-- url     : https://prove2.me/theorems/99998ac7-a52d-555a-bdaa-0b01af5e37a9
-- title:
--   Mem W0: aux integrable prod
-- statement:
--   The `L¹` consequence of `MemW0` on a Euclidean product.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1431-L1436
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1431-L1436

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_integrable_prod {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) : Integrable f := by sorry
