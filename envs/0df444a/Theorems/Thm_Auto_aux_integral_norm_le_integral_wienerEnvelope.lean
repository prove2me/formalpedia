-- Prove2me | Theorems.Thm_Auto_aux_integral_norm_le_integral_wienerEnvelope
-- name    : Auto.aux_integral_norm_le_integral_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:33.512982+00:00
-- url     : https://prove2.me/theorems/4e171f42-12d3-5845-ab59-975f69fadc0f
-- title:
--   Auto: aux integral norm le integral wiener Envelope
-- statement:
--   The elementary `L¹` estimate from the draft.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L999-L1003
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L999-L1003

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integral_norm_le_integral_wienerEnvelope {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) :
    (∫ x, ‖f x‖) ≤ ∫ x, wienerEnvelope f 1 x := by sorry
