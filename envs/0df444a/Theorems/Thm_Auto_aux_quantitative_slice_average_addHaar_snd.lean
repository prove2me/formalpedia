-- Prove2me | Theorems.Thm_Auto_aux_quantitative_slice_average_addHaar_snd
-- name    : Auto.aux_quantitative_slice_average_addHaar_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:44.926651+00:00
-- url     : https://prove2.me/theorems/50436484-6f18-4763-ab70-fa1f6b1bacaa
-- title:
--   Auto: aux quantitative slice average add Haar snd
-- statement:
--   Averaging over a unit ball gives a uniform bound for restriction to the second coordinate
--   slice on an arbitrary finite-dimensional additive Haar product.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1545-L1605
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1545-L1605

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_quantitative_slice_average_addHaar_snd {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]
    [Measure.IsAddHaarMeasure (volume : Measure F)]
    {H : E × F → ℝ} {G : E → ℝ} (hH : Integrable H (volume.prod volume))
    (hHnonneg : ∀ p, 0 ≤ H p) (hG : Continuous G) (hGnonneg : ∀ u, 0 ≤ G u)
    (v : F) (hpoint : ∀ v' ∈ closedBall v 1, ∀ u, G u ≤ H (u, v')) :
    (volume : Measure F).real (closedBall 0 1) * ∫ u, G u ≤ ∫ p, H p ∂(volume.prod volume) := by sorry
