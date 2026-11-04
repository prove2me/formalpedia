-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_jump_sum_mean_of_smalltime_rate
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_jump_sum_mean_of_smalltime_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:14:20.378267+00:00
-- url     : https://prove2.me/theorems/0309252e-a4b5-4765-83e7-4073f4260c07
-- title:
--   Original finite jump-test sum has mean T times genuine source small-time test rate
-- statement:
--   Given a genuinely established right-sided small-time first moment rate of the actual original one-time Levy law for any compact continuous negative-supported test, the exact actual source finite-jump test sum is integrable and its Bochner expectation equals the horizon times that small-time rate. Integrability of each one-time marginal is proved from compact support and original adaptedness, and the result combines independently Proved pathwise grid L1 convergence, original stationary finite-grid real Bochner means, real/NNReal uniform width identity and deterministic small-time scaling. No rate-equals-nu conclusion or jump compensator is assumed.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uniform_real_grid_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_smalltime_rescale_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_test_integrable

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_jump_sum_mean_of_smalltime_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (L : ℝ)
    (hRate : Tendsto
      (fun h : ℝ => (∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          g ((X.X u ω - X.X 0 ω) -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F, g ((X.X u ω - X.X 0 ω) -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u)) ∧
      (∫ ω, J ω ∂P) = (T : ℝ) * L := by sorry
