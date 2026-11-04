-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:57:15.557198+00:00
-- url     : https://prove2.me/theorems/7f2a0555-f7d4-4807-b76e-46afb62bfc90
-- title:
--   All original centred Lévy sample paths have the exact finite jump mesh-test limit
-- statement:
--   For every omega in the original SpectrallyNegativeLevy probability space, apply its proved zero-future centered path càdlàg interface to the deterministic theorem. The complete uniform-grid sum of continuous strictly negative compact test values converges to the finite actual marked jump sum of the same original centered sample path, without expectation or rate assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_exact_mesh_sum_from_positive_time_left_limits

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_original_centered_source_path_exact_mesh_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hneg : tsupport f ⊆ Set.Iio (0 : ℝ)) :
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω - X.X 0 ω
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        f (Y u - Function.leftLim Y u) ≠ 0) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ F, f (Y u - Function.leftLim Y u))) := by sorry
