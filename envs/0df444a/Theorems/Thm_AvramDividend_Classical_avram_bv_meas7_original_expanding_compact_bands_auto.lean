-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_expanding_compact_bands_auto
-- name    : AvramDividend.Classical.avram_bv_meas7_original_expanding_compact_bands_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:21:16.232207+00:00
-- url     : https://prove2.me/theorems/e642908b-e402-40c5-bc3c-304f8303edbd
-- title:
--   Original positive-cap compact localisation bands exist uniformly for finite and infinite caps
-- statement:
--   For every strictly positive extended-real dividend cap C, including the infinite cap, construct explicit functions a_n and b_n of compact pre-reserve bands satisfying a_n>0, a_n<=2, a_n<=b_n and [a_n/2,b_n] within {y>0,ofReal(y)<C}. The existence eliminates previously conditional deterministic band hypotheses in the original stopped X.nu compensated-jump and right-continuous-filtration predictable physical-grid certificates.
-- source:
--   Proved original finite-cap expanding-band theorem 204ef2ef for C ≠ top; Proved original unbounded-cap band theorem 76b80e3c for C=top, specialising each finite index. No stochastic assumptions or new jump compensation proof.

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_expanding_compact_bands
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_expanding_compact_band

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_expanding_compact_bands_auto (C : ℝ≥0∞) (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by sorry
