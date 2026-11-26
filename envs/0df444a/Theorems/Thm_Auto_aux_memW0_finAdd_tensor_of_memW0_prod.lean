-- Prove2me | Theorems.Thm_Auto_aux_memW0_finAdd_tensor_of_memW0_prod
-- name    : Auto.aux_memW0_finAdd_tensor_of_memW0_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:28.190804+00:00
-- url     : https://prove2.me/theorems/db634696-baeb-5821-9056-3ce1444c6433
-- title:
--   Auto: aux mem W0 fin Add tensor of mem W0 prod
-- statement:
--   The Euclidean binary tensor product belongs to `W₀` once its product-coordinate version does.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2465-L2486
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2465-L2486

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_memW0_finAdd_tensor_of_memW0_prod {n m : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} {g : EuclideanSpace ℝ (Fin m) → 𝕜}
    (hf : Continuous f) (hg : Continuous g)
    (hprod : MemW0 (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
      f p.1 * g p.2)) :
    MemW0 (fun z : EuclideanSpace ℝ (Fin (n + m)) ↦
      f (EuclideanSpace.finAddEquivProd z).1 * g (EuclideanSpace.finAddEquivProd z).2) := by sorry
