-- Prove2me | Theorems.Thm_Auto_MemW0_aux_memLp_one
-- name    : Auto.MemW0.aux_memLp_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:18.534494+00:00
-- url     : https://prove2.me/theorems/7f0fbe08-ec9b-4be7-9f91-028eea0ee70f
-- title:
--   Mem W0: aux mem Lp one
-- statement:
--   Consequently, `W₀` continuously embeds into `L¹`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L994-L996
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L994-L996

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_memLp_one {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) : MemLp f 1 volume := by sorry
