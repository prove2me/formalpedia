-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_finAdd_tensor_le
-- name    : Auto.aux_wienerEnvelope_finAdd_tensor_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:45:57.097088+00:00
-- url     : https://prove2.me/theorems/8e606751-eebb-5235-b302-e5f8f56100d0
-- title:
--   Auto: aux wiener Envelope fin Add tensor le
-- statement:
--   Pulling a binary tensor product back along the Euclidean coordinate splitting can only
--   decrease its local envelope.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2435-L2462
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2435-L2462

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_finAdd_tensor_le {n m : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} {g : EuclideanSpace ℝ (Fin m) → 𝕜}
    (hf : Continuous f) (hg : Continuous g) (z : EuclideanSpace ℝ (Fin (n + m))) :
    wienerEnvelope (fun w : EuclideanSpace ℝ (Fin (n + m)) ↦
      f (EuclideanSpace.finAddEquivProd w).1 * g (EuclideanSpace.finAddEquivProd w).2) 1 z ≤
      wienerEnvelope (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        f p.1 * g p.2) 1 (EuclideanSpace.finAddEquivProd z) := by sorry
