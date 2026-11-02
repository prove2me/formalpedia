-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_total_jump_intensity_gridfree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:00:49.648561+00:00
-- url     : https://prove2.me/theorems/4d7761f5-1504-4355-8d1b-8fa6d57926f1
-- title:
--   Original BV total intrinsic jump count has exact Lévy first-moment rate without a grid premise
-- statement:
--   For the actual original BV finite-negative-activity Lévy X, the literal source marked jump measure over (0,T] and all marks has expectation exactly T times X.ν(Iio 0). Unlike the previously established source first moment requiring auxiliary fine partitions, this interface has only intrinsic model hypotheses; a Proved deterministic grid witness supplies the required clock discretisation internally. This is the precise all-mark first-moment anchor for identifying the finite marked mean measure, not an independent Poisson copy or an arbitrary-mark compensator.
-- source:
--   Apply the canonically Proved uniform-grid witness and the original literal Poisson-count first moment d8534d75 directly on the same Ω,P,𝓕,X.X and ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_total_jump_intensity_gridfree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
