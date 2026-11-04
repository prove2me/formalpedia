-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:16:26.484742+00:00
-- url     : https://prove2.me/theorems/520707f5-45be-4033-8d0a-08544718b98e
-- title:
--   Original Levy finite jump-test sum is integrable and exact grid expectations converge to its genuine mean
-- statement:
--   For an original SpectrallyNegativeLevy process, every positive NNReal horizon and every continuous compactly supported negative-jump test, construct a single integrable random variable J. Identify J pointwise for every sample path with the exact finite nonzero left-limit jump-test sum on (0,T], and show the original uncentred uniform grids converge strongly in L1 and their genuine Bochner expectations converge to the integral of J. The deterministic jump set comes from the independently proved P2-H theorem; integrability and expectation convergence come from P2-J. This does not assume a jump compensator, Levy rate identity, or mesh limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Identify the integrable original-source limit with the genuine finite jump-test sum. -/

theorem AvramDividend.Classical.avram_p2_j_ui_original_finite_jump_sum_identified_integrable_mean
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
          g ((X.X u ω - X.X 0 ω) -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F, g ((X.X u ω - X.X 0 ω) -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u)) ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - J)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, J ω ∂P)) := by sorry
