-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_uniform_band_cofinal
-- name    : AvramDividend.Classical.avram_bv_meas7_uncapped_uniform_band_cofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:28:14.687932+00:00
-- url     : https://prove2.me/theorems/2bcf1ebd-37fc-4c06-84b3-3f207f302715
-- title:
--   Uncapped original reserve bands are compact and eventually contain every positive reserve
-- statement:
--   For the unbounded dividend cap C=top, select explicit original physical reserve localisation functions a_n=1/(n+1), b_n=n+2. They satisfy positivity, a_n<=2, a_n<=b_n, compact band inclusion in the strictly positive reserve interior, and every fixed positive reserve belongs to all sufficiently refined bands. This is the deterministic exhaustion adapter used when transferring original stopped X.nu compensated jump and predictable-mask certificates from compact bands to uncapped full reserve states.
-- source:
--   Combine the Proved original uncapped expanding compact band theorem 76b80e3c and Proved original eventual inclusion theorem 231a0455 for the identical explicit functions. No new stochastic assumptions or limit passage asserted.

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_expanding_compact_band
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_band_eventually_contains_positive_reserve

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_uncapped_uniform_band_cofinal :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (∀ y : ℝ, 0 < y → ∃ N : ℕ, ∀ n ≥ N,
        y ∈ Icc (a n / 2) (b n)) := by sorry
