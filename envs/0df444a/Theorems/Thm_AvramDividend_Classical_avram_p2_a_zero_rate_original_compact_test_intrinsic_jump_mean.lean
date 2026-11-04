-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_test_intrinsic_jump_mean
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_test_intrinsic_jump_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:27:09.617642+00:00
-- url     : https://prove2.me/theorems/2e2ebbae-ffd1-4839-991c-98de5de1115a
-- title:
--   Unconditional original Levy compact-negative intrinsic jump-test sum has prescribed Levy first moment
-- statement:
--   For the genuine original spectrally negative Levy process, combine P2-J's verified finite intrinsic-jump sum and strong grid-expectation convergence with original stationary-increment finite-grid expectations, P2-A's small-time source-rate mesh bridge and P2-I's prescribed Levy test integral. The source one-time integrability side condition follows independently from the genuine original coordinate measurability and the proved compact-negative finite envelope. This remains a compact-test first-moment statement; Borel extension and uncentred left-limit transport are separate.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_uniform_source_mean_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_marginal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_stationary_real_integral
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_test_intrinsic_jump_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hc : IsCompact (tsupport f)) (hneg : tsupport f ⊆ Iio (0 : ℝ))
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          f ((X.X u ω - X.X 0 ω) -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F, f ((X.X u ω - X.X 0 ω) -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u)) ∧
      (∫ ω, J ω ∂P) =
        (T : ℝ) * (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))) := by sorry
