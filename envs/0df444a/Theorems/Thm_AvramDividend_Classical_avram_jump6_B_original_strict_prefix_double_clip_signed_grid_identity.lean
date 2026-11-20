-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_prefix_double_clip_signed_grid_identity
-- name    : AvramDividend.Classical.avram_jump6_B_original_strict_prefix_double_clip_signed_grid_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:06:29.423438+00:00
-- url     : https://prove2.me/theorems/c4e29656-ddef-4cbe-b133-db65f9f86d47
-- title:
--   Exact true physical signed prefix equals the complete grid stopped at its prefix clock
-- statement:
--   For the actual canonical physical grid, clipping a second time at its index i clock leaves the first i cells unchanged, and every later cell has identical left and right endpoints. Consequently any signed physical-cell kernel g with g(t,t)=0 has total doubly clipped sum exactly equal to the original prefix through i-1, preserving the true stopped clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_earlier_prefix_equal_after_double_clipping
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_strict_prefix_double_clip_signed_grid_identity
    (j m i : ℕ) (hi : i ≤ m)
    (ρ : ℝ≥0) (g : ℝ≥0 → ℝ≥0 → ℝ)
    (hdiag : ∀ t, g t t = 0) :
    let u : ℕ → ℝ≥0 := fun k =>
      min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    let t : ℝ≥0 := u i
    let v : ℕ → ℝ≥0 := fun k =>
      min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    (∑ l ∈ Finset.range m, g (v (l + 1)) (v l)) =
      (∑ l ∈ Finset.range i, g (u (l + 1)) (u l)) := by sorry
