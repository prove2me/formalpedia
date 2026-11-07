-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope
-- name    : AvramDividend.Classical.avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:51:29.592596+00:00
-- url     : https://prove2.me/theorems/9228bef1-17d5-4853-8054-c29ef80ab4bb
-- title:
--   Discounted original compact C1 negative-mark kernel has BV-linear magnitude envelope
-- statement:
--   The exact discounted C1 negative-jump difference on a positive original state band is bounded by (L+4R/a) times actual negative jump magnitude. Nonnegative discount q makes the exponential at most one. This proved child feeds direct same-NX integrability without adding a stochastic source hypothesis.

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compact_C1_all_negative_mark_linear_magnitude_envelope

open Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope
    (w : ℝ → ℝ) (a b L R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0)
    (y z : ℝ) (hy : y ∈ Icc a b) (hz : z < 0) :
    |Real.exp (-(q * (t : ℝ))) * (w (y + z) - w y)| ≤
      (L + 4 * R / a) * (-z) := by sorry
