-- Prove2me | Theorems.Thm_Auto_aux_continuous_integral_slice
-- name    : Auto.aux_continuous_integral_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:39.725909+00:00
-- url     : https://prove2.me/theorems/5c118fc7-c57e-4463-ba72-7b441bfdb250
-- title:
--   Auto: aux continuous integral slice
-- statement:
--   Integration along the second coordinate is continuous on `W₀`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1903-L1940
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1903-L1940

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_continuous_integral_slice {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) :
    Continuous (fun u ↦ ∫ v, f (u, v)) := by sorry
