-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_comp_linearIsometryEquiv
-- name    : Auto.aux_wienerEnvelope_comp_linearIsometryEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:45.223799+00:00
-- url     : https://prove2.me/theorems/a2057e3f-3302-4d60-b960-ce56fb6a0240
-- title:
--   Auto: aux wiener Envelope comp linear Isometry Equiv
-- statement:
--   An isometric linear change of finite-dimensional Euclidean coordinates preserves the unit
--   local envelope exactly.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L340-L358
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L340-L358

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerEnvelope_comp_linearIsometryEquiv {E F K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup K]
    (e : E ≃ₗᵢ[ℝ] F) {f : F → K} (x : E) :
    wienerEnvelope (f ∘ e) 1 x = wienerEnvelope f 1 (e x) := by sorry
