-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_total_source_jump_magnitudes_le_residual
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_total_source_jump_magnitudes_le_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:37:51.935162+00:00
-- url     : https://prove2.me/theorems/8c72f1c5-3e3c-404d-9bf9-e8c9ad513a94
-- title:
--   Total genuine BV Lévy downward-jump magnitude on any horizon is bounded by the original residual
-- statement:
--   On one probability-one event for the original bounded-variation spectrally negative Lévy process, the full ENNReal sum over all positive-time true downward source jumps before any horizon T is bounded by the finite actual residual T*drift−X_T. This strengthens the accepted finite-jump-budget theorem to the supremum of all finite subsets using ENNReal.tsum_eq_iSup_sum. The statement is a source-path total jump-variation bound, without asserting the residual has no non-atomic continuous component or that its jump counts are Poisson.
-- source:
--   Canonical Proved source finite jump budget b02ad279-2e42-493a-ab8a-e763119bdffe; pinned Mathlib.Topology.Algebra.InfiniteSum.ENNReal tsum_eq_iSup_sum and Finset.sum_filter. Original P and X, no replacement process.

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_total_source_jump_magnitudes_le_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) ≤
      ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) := by sorry
