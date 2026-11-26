-- Prove2me | Theorems.Thm_Auto_MemW0_aux_memW0_slice
-- name    : Auto.MemW0.aux_memW0_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:35.105831+00:00
-- url     : https://prove2.me/theorems/01837c8a-4d09-5c0e-b14e-1e2efe02bfcc
-- title:
--   Mem W0: aux mem W0 slice
-- statement:
--   Restricting a Wiener-space function on a Euclidean product to any coordinate fibre again
--   gives a Wiener-space function.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1442-L1468
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1442-L1468

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_memW0_slice {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) (u : EuclideanSpace ℝ (Fin m)) :
    MemW0 (fun v ↦ f (u, v)) := by sorry
