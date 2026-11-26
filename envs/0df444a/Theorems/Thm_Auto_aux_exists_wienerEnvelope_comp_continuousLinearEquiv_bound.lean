-- Prove2me | Theorems.Thm_Auto_aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound
-- name    : Auto.aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:26.124014+00:00
-- url     : https://prove2.me/theorems/4083bc3a-e9f6-4317-a235-3970d98a3255
-- title:
--   Auto: aux exists wiener Envelope comp continuous Linear Equiv bound
-- statement:
--   An invertible finite-dimensional linear change of variables has a uniform Wiener-integral
--   bound.  The constant depends only on the change of coordinates (through its Haar scalar and a
--   finite cover of its operator-norm ball).
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L730-L778
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L730-L778

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] (e : E ≃L[ℝ] F) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : F → K, MemW0 f →
      (∫ x, wienerEnvelope (f ∘ e) 1 x) ≤ C * ∫ y, wienerEnvelope f 1 y := by sorry
