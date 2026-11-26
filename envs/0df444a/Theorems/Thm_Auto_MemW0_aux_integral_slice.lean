-- Prove2me | Theorems.Thm_Auto_MemW0_aux_integral_slice
-- name    : Auto.MemW0.aux_integral_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:35.757962+00:00
-- url     : https://prove2.me/theorems/d4717a0a-b356-5700-aace-f894cbfc044c
-- title:
--   Mem W0: aux integral slice
-- statement:
--   The coordinate fibre-integral theorem from the draft.  It is the case of the source's
--   injective map `π` given by the canonical product coordinates.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1946-L1979
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1946-L1979

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_integral_slice {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) :
    MemW0 (fun u ↦ ∫ v, f (u, v)) := by sorry
