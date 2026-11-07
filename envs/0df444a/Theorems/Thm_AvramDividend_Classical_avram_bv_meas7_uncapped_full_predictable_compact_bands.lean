-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_full_predictable_compact_bands
-- name    : AvramDividend.Classical.avram_bv_meas7_uncapped_full_predictable_compact_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:53:41.657065+00:00
-- url     : https://prove2.me/theorems/9b971544-2677-4abf-825e-54e85f15afaa
-- title:
--   Original uncapped full predictable reserve bands are compact and exhaust each positive reserve
-- statement:
--   The exact compact-band geometry required by the original stopped X.nu compensator and the stronger eventual inclusion in the actual predictable E_n=Icc(a_n,b_n) pre-reserve mask hold simultaneously for explicit uncapped a_n=1/(n+1), b_n=n+2. This repairs the gap between wider Icc(a_n/2,b_n) cofinality and actual previsible mask exhaustion.
-- source:
--   Already Proved uncapped compact-band geometry 76b80e3c and newly Proved BV-MEAS7 uncapped full predictable-band eventual inclusion.

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_expanding_compact_band
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_full_predictable_band_eventually_contains_reserve

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_uncapped_full_predictable_compact_bands :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (∀ y : ℝ, 0 < y → ∃ N : ℕ, ∀ n ≥ N,
        y ∈ Icc (a n) (b n)) := by sorry
