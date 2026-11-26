-- Prove2me | Theorems.Thm_Auto_MemW0_aux_fintype_tensor_comp_of_iInf_ker_eq_bot
-- name    : Auto.MemW0.aux_fintype_tensor_comp_of_iInf_ker_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:55:32.621431+00:00
-- url     : https://prove2.me/theorems/9581616b-6c37-44e2-ba45-44efbc2ea976
-- title:
--   Mem W0: aux fintype tensor comp of i Inf ker eq bot
-- statement:
--   The kernel-intersection hypothesis in the Brascamp--Lieb consequence yields the required
--   injectivity of its simultaneous pullback.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2695-L2705
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2695-L2705

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_fintype_tensor_comp_of_iInf_ker_eq_bot
    {ι : Type*} [Fintype ι] {m l : ℕ} {d : ι → ℕ}
    {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, MemW0 (f i))
    (π : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hker : ⨅ i, LinearMap.ker (π i).toLinearMap = ⊥) :
    MemW0 (fun uv : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) ↦
      ∏ i, f i (π i uv)) := by sorry
