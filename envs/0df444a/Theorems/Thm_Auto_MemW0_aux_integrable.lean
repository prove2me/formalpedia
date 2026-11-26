-- Prove2me | Theorems.Thm_Auto_MemW0_aux_integrable
-- name    : Auto.MemW0.aux_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:42:36.809998+00:00
-- url     : https://prove2.me/theorems/f7b54610-1352-598d-806f-57df2bc65428
-- title:
--   Mem W0: aux integrable
-- statement:
--   The `L¹` part of the Wiener-space embedding.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L985-L991
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L985-L991

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_integrable {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) : Integrable f := by sorry
