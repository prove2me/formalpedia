-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate
-- name    : AvramDividend.Classical.avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T20:21:31.440486+00:00
-- url     : https://prove2.me/theorems/788041e5-e0e4-48be-83b2-5d12b01273ca
-- title:
--   Genuine original Lévy ν intensity on Borel negative jump mark sets bounded away from zero
-- statement:
--   For the unchanged source process X on Ω/P and any Borel mark band B contained in (-∞,-ε] with ε>0, prove the genuine original intrinsic negative jump expected count on (s,t] equals (t-s)ν(B). This is the exact finite-band Lévy–Itô identification step, with no assumed compensation law, no Poisson replacement, no BV and no finite activity. Since the original Lévy integrability makes ν finite on every separated band, the harder general infinite-activity Borel rate then follows from the monotone-band exhaustion theorem 42393902. Source small-time weighted exponential fourth moments already identify the same original ν transforms; the missing analytic bridge is convergence of intrinsic jump counts from marginal/grid small-time data.
-- source:
--   Exact original SpectrallyNegativeLevy definition, original weighted fourth small-time ν moment e6973988, original Borel marked grid mean 20fc3267, source finite path jumps on separated bands 557aabfa. Strictly narrower mathematical leaf for 4928a464.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
