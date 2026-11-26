-- Prove2me | Theorems.Thm_Auto_aux_integrable_wienerEnvelope_mul_prod
-- name    : Auto.aux_integrable_wienerEnvelope_mul_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:08.191283+00:00
-- url     : https://prove2.me/theorems/c33dd568-99bd-406e-b36e-0f9a541370aa
-- title:
--   Auto: aux integrable wiener Envelope mul prod
-- statement:
--   A product of two integrable nonnegative local envelopes is integrable on the product.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2116-L2151
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2116-L2151

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integrable_wienerEnvelope_mul_prod {E F 𝕜 : Type*} [NormedAddCommGroup E]
    [ProperSpace E] [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [NormedAddCommGroup F] [ProperSpace F] [MeasureSpace F] [BorelSpace F]
    [SFinite (volume : Measure F)]
    [NormedField 𝕜] {f : E → 𝕜} {g : F → 𝕜} (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable (wienerEnvelope f 1)) (hgi : Integrable (wienerEnvelope g 1)) :
    Integrable (fun x : E × F ↦ wienerEnvelope f 1 x.1 * wienerEnvelope g 1 x.2) := by sorry
