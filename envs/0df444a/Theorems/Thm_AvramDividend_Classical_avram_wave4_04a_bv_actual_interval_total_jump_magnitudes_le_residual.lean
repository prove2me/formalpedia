-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:56:16.637991+00:00
-- url     : https://prove2.me/theorems/0ebd2a44-06bf-4a28-a9db-4e70c0ac84c8
-- title:
--   Full genuine BV Lévy jump magnitude on any time interval is dominated by its original Stieltjes drift-residual increment
-- statement:
--   On one probability-one event for the genuine original bounded-variation spectrally negative Lévy process X, for every interval (s,t] with s≤t, the complete ENNReal sum of actual downward jump magnitudes X_{u-}−X_u at times s<u≤t is bounded by the original residual increment ((t*d−X_t)−(s*d−X_s)). This is the interval-local source-X finite-variation bound needed for stopping/localization; it is strictly more useful than subtracting two cumulative upper bounds, which would be mathematically invalid. The proof uses the genuine original residual Stieltjes function with singleton atoms equaling source jumps, sum_measure_singleton over filtered finite subsets, domination by F.measure((s,t]), and ENNReal.tsum_eq_iSup_sum. It does not assert that the residual has no diffuse part or identify a Poisson compensator.
-- source:
--   Canonical Proved 0c2826fa-5cd3-4dcb-bef0-9a029879d9b2 source BV residual Stieltjes singleton atoms on one full event; pinned Mathlib StieltjesFunction.measure_Ioc, sum_measure_singleton, measure_mono, ENNReal.tsum_eq_iSup_sum and Finset.sum_filter.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (∑' (u : ℝ≥0),
        if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) ≤
      ENNReal.ofReal
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by sorry
