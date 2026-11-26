-- Prove2me | Theorems.Thm_Auto_MemW0_aux_fintype_tensor_comp_injective
-- name    : Auto.MemW0.aux_fintype_tensor_comp_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:49:35.670536+00:00
-- url     : https://prove2.me/theorems/49be3a7e-98d5-4791-8923-c60e3bede3fd
-- title:
--   Mem W0: aux fintype tensor comp injective
-- statement:
--   An injective simultaneous linear pullback of a finite tensor product belongs to `W₀`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2634-L2668
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2634-L2668

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_fintype_tensor_comp_injective
    {ι : Type*} [Fintype ι] {m l : ℕ} {d : ι → ℕ}
    {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, MemW0 (f i))
    (π : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hπ : Function.Injective (ContinuousLinearMap.pi π)) :
    MemW0 (fun uv : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) ↦
      ∏ i, f i (π i uv)) := by sorry
