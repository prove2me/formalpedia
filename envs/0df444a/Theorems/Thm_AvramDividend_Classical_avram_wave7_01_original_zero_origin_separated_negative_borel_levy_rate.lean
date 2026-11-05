-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
-- name    : AvramDividend.Classical.avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:39:06.887281+00:00
-- url     : https://prove2.me/theorems/34dbea70-e487-4806-9b05-464d4f8d052e
-- title:
--   Actual original Lévy zero-origin separated negative Borel jump count has prescribed ν rate
-- statement:
--   For the original Lévy X on exactly Ω/P, establish the first moment E N_X((0,T]×B)=T ν(B) at the zero time origin for arbitrary Borel negative jump band B bounded away from 0. No finite activity, BV, replacement process or assumed compensator. This isolates the original Lévy–Khintchine analytic jump-rate identification from stationary time transport, allowing arbitrary s,t subsequently by independent genuine source stationarity.
-- source:
--   Original small-time fourth-weighted ν Laplace derivative e6973988, actual original finite-grid marked mean 20fc3267; original jump path convergence on separated bands.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) =
      (T : ℝ≥0∞) * X.ν B := by sorry
