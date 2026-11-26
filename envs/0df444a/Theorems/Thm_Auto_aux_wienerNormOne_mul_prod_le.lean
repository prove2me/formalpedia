-- Prove2me | Theorems.Thm_Auto_aux_wienerNormOne_mul_prod_le
-- name    : Auto.aux_wienerNormOne_mul_prod_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:06.366545+00:00
-- url     : https://prove2.me/theorems/670107a8-d041-569e-9363-c91482d27224
-- title:
--   Auto: aux wiener Norm One mul prod le
-- statement:
--   The quantitative binary tensor-product estimate for the extended Wiener integrals.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2172-L2196
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2172-L2196

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerNormOne_mul_prod_le {E F 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)] [NormedField 𝕜]
    {f : E → 𝕜} {g : F → 𝕜}
    (hf : Continuous f) (hg : Continuous g) :
    wienerNormOne (fun x : E × F ↦ f x.1 * g x.2) ≤ wienerNormOne f * wienerNormOne g := by sorry
