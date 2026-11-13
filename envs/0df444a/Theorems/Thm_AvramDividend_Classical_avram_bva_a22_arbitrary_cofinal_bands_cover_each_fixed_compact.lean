-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_arbitrary_cofinal_bands_cover_each_fixed_compact
-- name    : AvramDividend.Classical.avram_bva_a22_arbitrary_cofinal_bands_cover_each_fixed_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:55:42.563362+00:00
-- url     : https://prove2.me/theorems/82ba7e11-13cd-4ec3-9bb5-cc4a34290c2b
-- title:
--   Every prescribed cofinal original spatial band family eventually covers each fixed strict compact interval
-- statement:
--   For arbitrary original spatial localisation bands a(n),b(n) satisfying pointwise eventual coverage of each strictly positive state below cap C, prove that every fixed compact subinterval [c,d] strictly inside the cap is eventually included in each band, uniformly over every point of the interval. The proof takes the maximum of the two endpoint cofinality indices and uses convexity of closed intervals. Unlike an arbitrarily chosen fast diagonal, this preserves the actual prescribed bands of BVA63/BVA96. It is a source-independent localisation lemma; it does not claim moving physical-grid states or stochastic error mean convergence.

import Mathlib
open Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_arbitrary_cofinal_bands_cover_each_fixed_compact
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C) :
    ∃ N : ℕ, ∀ n ≥ N, Icc c d ⊆ Icc (a n) (b n) := by sorry
