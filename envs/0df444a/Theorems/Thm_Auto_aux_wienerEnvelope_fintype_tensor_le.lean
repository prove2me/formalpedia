-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_fintype_tensor_le
-- name    : Auto.aux_wienerEnvelope_fintype_tensor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:14.841436+00:00
-- url     : https://prove2.me/theorems/d61cec35-20a1-414e-98ed-49a18c884c36
-- title:
--   Auto: aux wiener Envelope fintype tensor le
-- statement:
--   The local envelope of a finite tensor product is at most the product of the individual
--   local envelopes.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2536-L2556
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2536-L2556

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_fintype_tensor_le {ι : Type*} [Fintype ι]
    {d : ι → ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, Continuous (f i))
    (x : ∀ i, EuclideanSpace ℝ (Fin (d i))) :
    wienerEnvelope (fun y : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (y i)) 1 x ≤
      ∏ i, wienerEnvelope (f i) 1 (x i) := by sorry
