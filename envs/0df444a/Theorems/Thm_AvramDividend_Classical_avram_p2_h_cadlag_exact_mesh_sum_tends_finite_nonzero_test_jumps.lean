-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_exact_mesh_sum_tends_finite_nonzero_test_jumps
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_exact_mesh_sum_tends_finite_nonzero_test_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:36:55.51856+00:00
-- url     : https://prove2.me/theorems/2b60c7dd-f2ce-490a-819d-c0b7a2b068ef
-- title:
--   Exact continuous negative-test uniform mesh limit over genuinely finite nonzero càdlàg jumps
-- statement:
--   For a real-valued path with right continuity and canonical strict-left limits, a positive nonnegative-time horizon and a continuous real test whose closed support is strictly negative, the full uniform right-closed mesh sum tends exactly to the finite sum over those and only those original jump times with nonzero test weight. Includes the initial/horizon and exact aligned-grid conventions; entirely deterministic, without rate, expectation or compensator assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_strict_negative_tsupport_gives_zero_near_origin
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_sum_tends_to_all_large_actual_jumps

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_exact_mesh_sum_tends_finite_nonzero_test_jumps
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hneg : tsupport f ⊆ Set.Iio (0 : ℝ))
    (hL : ∀ t : ℝ≥0,
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
