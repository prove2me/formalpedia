-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_exact_mesh_sum_from_positive_time_left_limits
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_exact_mesh_sum_from_positive_time_left_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:46:39.116508+00:00
-- url     : https://prove2.me/theorems/edd6be9b-834c-466e-b174-2c5224df48b3
-- title:
--   Exact mesh-to-finite-jump equality under the source standard càdlàg hypotheses
-- statement:
--   Apply the complete deterministic exact uniform mesh-to-jump theorem to the source-compatible càdlàg interface: right continuity at every nonnegative time and canonical left limits only at strictly positive times, where the initial-time left filter is vacuous. The finite sum includes exactly actual nonzero continuous-test jumps in (0,T].

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_strict_left_limit_at_zero_is_vacuous
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_exact_mesh_sum_tends_finite_nonzero_test_jumps

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_exact_mesh_sum_from_positive_time_left_limits
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hneg : tsupport f ⊆ Set.Iio (0 : ℝ))
    (hL : ∀ t : ℝ≥0, 0 < t →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        f (Y u - Function.leftLim Y u) ≠ 0) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ F, f (Y u - Function.leftLim Y u))) := by sorry
