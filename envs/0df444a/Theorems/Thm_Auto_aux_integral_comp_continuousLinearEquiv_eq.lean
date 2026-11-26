-- Prove2me | Theorems.Thm_Auto_aux_integral_comp_continuousLinearEquiv_eq
-- name    : Auto.aux_integral_comp_continuousLinearEquiv_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:43.56807+00:00
-- url     : https://prove2.me/theorems/722184ec-2a6f-5b69-886e-590c364bc094
-- title:
--   Auto: aux integral comp continuous Linear Equiv eq
-- statement:
--   Change of variables for an invertible finite-dimensional linear map, with the Haar
--   normalization factor made explicit.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L400-L423
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L400-L423

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integral_comp_continuousLinearEquiv_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    (e : E ≃L[ℝ] F) {g : F → ℝ} (hg : Continuous g) :
    (∫ x, g (e x)) =
      (Measure.addHaarScalarFactor (Measure.map (e : E → F) volume) volume : ℝ) *
        ∫ y, g y := by sorry
