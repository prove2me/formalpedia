-- Prove2me | Theorems.Thm_Auto_aux_continuous_fintype_tensor
-- name    : Auto.aux_continuous_fintype_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:29.509225+00:00
-- url     : https://prove2.me/theorems/d7f64af2-89d1-526d-b7f8-2221dd91e218
-- title:
--   Auto: aux continuous fintype tensor
-- statement:
--   A finite tensor product of continuous functions is continuous.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2525-L2530
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2525-L2530

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_continuous_fintype_tensor {ι : Type*} [Fintype ι]
    {d : ι → ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (x i)) := by sorry
