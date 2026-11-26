-- Prove2me | Theorems.Thm_Auto_MemW0_aux_memLp_top
-- name    : Auto.MemW0.aux_memLp_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:47:35.25436+00:00
-- url     : https://prove2.me/theorems/cf1b275a-30d4-51be-ab86-e0d4e3ee7ea6
-- title:
--   Mem W0: aux mem Lp top
-- statement:
--   Consequently, `W₀` continuously embeds into `L∞`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1066-L1071
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1066-L1071

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_memLp_top {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) : MemLp f ∞ volume := by sorry
