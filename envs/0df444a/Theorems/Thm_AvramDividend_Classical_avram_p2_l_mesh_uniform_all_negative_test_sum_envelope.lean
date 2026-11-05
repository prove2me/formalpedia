-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_all_negative_test_sum_envelope
-- name    : AvramDividend.Classical.avram_p2_l_mesh_uniform_all_negative_test_sum_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:53:45.546621+00:00
-- url     : https://prove2.me/theorems/30348f4d-4e16-4944-b787-fe781afdac78
-- title:
--   Uniform eventual marked-sum envelope over all bounded negative-supported tests
-- statement:
--   One fine original uniform mesh controls all bounded negative-supported real test sums simultaneously, without requiring continuity, boundary-atom avoidance or measurability.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_all_negative_mark_count_envelope

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_uniform_all_negative_test_sum_envelope
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ,
        (∀ z : ℝ, -ρ < z → f z = 0) →
        ∀ M : ℝ, 0 ≤ M → (∀ z : ℝ, |f z| ≤ M) →
        |∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))| ≤
          (S.card : ℝ) * M := by sorry
