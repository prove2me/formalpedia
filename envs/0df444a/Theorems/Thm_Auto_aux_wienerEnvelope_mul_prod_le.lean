-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_mul_prod_le
-- name    : Auto.aux_wienerEnvelope_mul_prod_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:50.171797+00:00
-- url     : https://prove2.me/theorems/db0e6f74-c2b0-4792-8fbf-b1f6d43e054a
-- title:
--   Auto: aux wiener Envelope mul prod le
-- statement:
--   The local envelope of a tensor product is bounded by the product of the local envelopes.
--   The ambient product has its standard max metric.
--   Thus, a unit ball is a product of unit balls.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2093-L2113
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2093-L2113

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_mul_prod_le {E F 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] [ProperSpace F] [NormedField 𝕜] {f : E → 𝕜} {g : F → 𝕜}
    (hf : Continuous f) (hg : Continuous g) (x : E × F) :
    wienerEnvelope (fun p : E × F ↦ f p.1 * g p.2) 1 x ≤
      wienerEnvelope f 1 x.1 * wienerEnvelope g 1 x.2 := by sorry
