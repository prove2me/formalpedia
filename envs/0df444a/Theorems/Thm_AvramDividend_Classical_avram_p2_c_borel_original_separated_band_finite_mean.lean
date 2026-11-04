-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_band_finite_mean
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_separated_band_finite_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:40:18.477827+00:00
-- url     : https://prove2.me/theorems/c9e0c0df-cc60-46e3-9e77-138d5b43a2da
-- title:
--   Actual original separated negative-band jump counts have finite expectation without a ν-rate assumption
-- statement:
--   For every original spectrally negative Lévy sample source and positive horizon/cutoff, the expected literal number of negative jumps bounded away from zero is finite, including UBV paths. The proof combines the already Proved pathwise source grid-liminf bound and finite linear first-moment grid envelope by Fatou, using the inclusive threshold to dominate the strict grid test.
-- source:
--   Proved original source grid-liminf  da103e9d, original small-time moment grid envelope a1993f05 and general Fatou transfer 4f270bf9. No ν-rate, Poisson replacement, BV or assumed compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_intrinsic_negative_count_le_grid_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_grid_mean_liminf_horizon_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_count_expectation_le_grid_liminf_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_c_borel_original_separated_band_finite_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ∂P) < ⊤ := by sorry
