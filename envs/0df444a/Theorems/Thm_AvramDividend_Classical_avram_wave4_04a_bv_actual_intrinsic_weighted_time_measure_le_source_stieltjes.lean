-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_weighted_time_measure_le_source_stieltjes
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_weighted_time_measure_le_source_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:23:52.394746+00:00
-- url     : https://prove2.me/theorems/5ffa01b6-5822-44c8-9ec7-dbbe7eb28ea8
-- title:
--   Original BV Lévy intrinsic weighted jump counting measure is dominated by its actual residual Stieltjes measure on every Borel time set
-- statement:
--   On one probability-one event of the genuine original BV spectrally negative Lévy process X, the N_X(ω)-integral of the negative mark magnitude restricted to any Borel time set B is dominated by the actual drift-deficit Stieltjes measure F.measure B with F(t)=t*X.drift−X_t(ω). The bound holds for all measurable B simultaneously, enabling stopped/reserve-dependent Borel sections. N_X is literally the count restriction on original jump times mapped by (u,ΔX_u). This is a pathwise uncompensated measure domination, not the Lévy predictable compensator ds⊗ν, nor a Poisson count law.
-- source:
--   Proved original path N_X lintegral-to-jump-sum theorem e4542c93-c64b-453a-b582-e5ec26265dfc; source BV all-measurable-time-sets Stieltjes atom domination target AvramDividend.Classical.avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets (canonically Proved UUID 6db7ca71-b2a6-468c-9020-c8178e8d9dd3, accepted candidate 19722). ENNReal.measurable_ofReal and tsum_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_weighted_time_measure_le_source_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      (∀ (B : Set ℝ≥0), MeasurableSet B →
        (∫⁻ p,
          (if p.1 ∈ B then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
        F.measure B) := by sorry
