-- Prove2me | Theorems.Thm_Auto_aux_memW0_comp_finAddEquivProd_symm
-- name    : Auto.aux_memW0_comp_finAddEquivProd_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:14.335036+00:00
-- url     : https://prove2.me/theorems/46fe60ff-9fdb-581d-8601-aa477b82fd37
-- title:
--   Auto: aux mem W0 comp fin Add Equiv Prod symm
-- statement:
--   Transport a Wiener-space function from Euclidean coordinates to the corresponding product
--   coordinates.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2222-L2247
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2222-L2247

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_memW0_comp_finAddEquivProd_symm {n m : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin (n + m)) → 𝕜}
    (hf : MemW0 f) :
    MemW0 (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
      f (EuclideanSpace.finAddEquivProd.symm p)) := by sorry
