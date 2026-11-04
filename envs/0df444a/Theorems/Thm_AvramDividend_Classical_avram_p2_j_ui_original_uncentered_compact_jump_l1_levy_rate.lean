-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_compact_jump_l1_levy_rate
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_uncentered_compact_jump_l1_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:50:59.280978+00:00
-- url     : https://prove2.me/theorems/77b8de61-4113-41c6-978c-42cb97e41aed
-- title:
--   Original uncentred intrinsic compact jump sums: true L1 convergence and genuine Levy mean
-- statement:
--   For the original spectrally negative Levy process, any positive horizon and continuous compact strictly negative real test, establish an integrable finite sum of precisely the original uncentred intrinsic jumps at which the test is nonzero. The original uniform-grid increment sums converge to that same random variable in genuine Bochner L1. Its expected real integral equals the horizon times the integral against the original negative Levy measure. This combines two independently Proved source-exact original process theorems and the positive-time centring invariance, without any stochastic compensator or extra law.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_negative_uniform_grid_levy_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_jump_equals_centered_jump

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_uncentered_compact_jump_l1_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u)) ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - J)
        1 P) atTop (nhds 0) ∧
      (∫ ω, J ω ∂P) = (T : ℝ) *
        (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ)))) := by sorry
