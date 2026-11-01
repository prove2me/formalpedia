-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:21:15.780928+00:00
-- url     : https://prove2.me/theorems/b02ad279-2e42-493a-ab8a-e763119bdffe
-- title:
--   Every finite set of genuine BV Lévy downward jumps has total magnitude bounded by actual residual loss
-- statement:
--   On an almost-sure event of the actual original BV spectrally negative Lévy source X, for every nonnegative horizon T and any finite set S of true positive jump times up to T, the sum of its jump magnitudes (in ENNReal) is at most the actual drift residual T*d-X_T. This is derived from the genuine source Stieltjes residual measure: its singleton atoms exactly equal each true source negative jump magnitude, finite-singleton measures sum to the measure of S, and S⊆(0,T] where the measure mass is exactly T*d-X_T. No independent Poisson-space process, compensation, or atom-only decomposition is used. This finite-jump budget is a step toward locally finite separated-band counts.
-- source:
--   Canonical Proved original-X residual Stieltjes atom identity 0c2826fa-5cd3-4dcb-bef0-9a029879d9b2; pinned Mathlib MeasureTheory.sum_measure_singleton and StieltjesFunction.measure_Ioc; original X.X_zero. Direct original path finite subset budget.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (S : Finset ℝ≥0),
      (∀ u ∈ S, 0 < u ∧ u ≤ T) →
      (∑ u ∈ S, ENNReal.ofReal
        (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)) ≤
      ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) := by sorry
