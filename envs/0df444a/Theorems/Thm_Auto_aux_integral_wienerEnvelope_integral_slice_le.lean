-- Prove2me | Theorems.Thm_Auto_aux_integral_wienerEnvelope_integral_slice_le
-- name    : Auto.aux_integral_wienerEnvelope_integral_slice_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:41.260282+00:00
-- url     : https://prove2.me/theorems/193d37b1-8e63-5587-ad25-9208b88a1d40
-- title:
--   Auto: aux integral wiener Envelope integral slice le
-- statement:
--   The quantitative estimate for the coordinate fibre integral: its unit Wiener integral is at
--   most that of the original function.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1985-L2023
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1985-L2023

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integral_wienerEnvelope_integral_slice_le {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) :
    (∫ u, wienerEnvelope (fun u ↦ ∫ v, f (u, v)) 1 u) ≤
      ∫ p, wienerEnvelope f 1 p := by sorry
