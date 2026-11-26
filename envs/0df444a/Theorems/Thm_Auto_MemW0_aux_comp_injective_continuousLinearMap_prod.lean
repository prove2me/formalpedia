-- Prove2me | Theorems.Thm_Auto_MemW0_aux_comp_injective_continuousLinearMap_prod
-- name    : Auto.MemW0.aux_comp_injective_continuousLinearMap_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:56.237049+00:00
-- url     : https://prove2.me/theorems/b896103b-73ce-5ec0-865e-a049535c02e1
-- title:
--   Mem W0: aux comp injective continuous Linear Map prod
-- statement:
--   Pullback along an injective linear map with a product Euclidean domain preserves `W₀`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2250-L2265
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2250-L2265

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.aux_comp_injective_continuousLinearMap_prod
    {m l n : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} (hf : MemW0 f)
    (π : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (hπ : Function.Injective π) :
    MemW0 (fun uv => f (π uv)) := by sorry
