-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_uniform_source_mean_rate
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_uniform_source_mean_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:02:16.391681+00:00
-- url     : https://prove2.me/theorems/84ff152c-f227-49c7-a36a-05fdb0c7a181
-- title:
--   Original Levy compact-negative source expected uniform-grid rate equals horizon times genuine Levy integral
-- statement:
--   For the original spectrally negative Levy process X, ordinary real positive-time normalized compact negative test convergence from P2-I together with the P2-K uniform mesh algebra gives n+1 times the original single-cell test expectation converging to T times the integral against the actual X.nu, with no compensator or alternate process.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_compact_test_real_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_uniform_mesh_tendsto_positive_smalltime
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_rate_uniform_grid_algebra_bridge
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_uniform_source_mean_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      (∫ ω, f (X.X (Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω) ∂P))
      atTop (𝓝 ((T : ℝ) *
        (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))))) := by sorry
