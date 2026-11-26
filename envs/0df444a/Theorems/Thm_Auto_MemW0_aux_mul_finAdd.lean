-- Prove2me | Theorems.Thm_Auto_MemW0_aux_mul_finAdd
-- name    : Auto.MemW0.aux_mul_finAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:54:47.840654+00:00
-- url     : https://prove2.me/theorems/08160241-6e8a-43b4-977b-e847fe4b3d16
-- title:
--   Mem W0: aux mul fin Add
-- statement:
--   The finite-dimensional tensor-product property in Euclidean coordinates.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2489-L2494
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2489-L2494

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_mul_finAdd {n m : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} {g : EuclideanSpace ℝ (Fin m) → 𝕜}
    (hf : MemW0 f) (hg : MemW0 g) :
    MemW0 (fun z : EuclideanSpace ℝ (Fin (n + m)) ↦
      f (EuclideanSpace.finAddEquivProd z).1 * g (EuclideanSpace.finAddEquivProd z).2) := by sorry
