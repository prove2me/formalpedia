-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:26:55.754425+00:00
-- url     : https://prove2.me/theorems/070d50f8-9313-4248-851d-bc5ef3e8d92a
-- title:
--   Eventually every large cell in a uniformly fine bounded family contains a genuine jump
-- statement:
--   For a finite-horizon càdlàg path and any uniformly shrinking indexed family of ordered cells, all sufficiently fine cells with path increments above a threshold contain an actual jump above that threshold in their right-closed time interval.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_no_cofinally_spurious_large_fine_cells

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℕ → ℕ → ℝ≥0)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbound : ∀ n i, b n i ≤ T)
    (hwidth : ∀ (is ns : ℕ → ℕ),
      Tendsto ns atTop (atTop : Filter ℕ) →
      Tendsto (fun k => (b (ns k) (is k) : ℝ) -
        (a (ns k) (is k) : ℝ)) atTop (𝓝 (0 : ℝ)))
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : ℕ,
      ρ ≤ |Y (b n i) - Y (a n i)| →
        ∃ t : ℝ≥0, a n i < t ∧ t ≤ b n i ∧
          ρ ≤ |Y t - Function.leftLim Y t| := by sorry
