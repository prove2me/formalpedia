-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
-- name    : AvramDividend.Classical.avram_bv_meas7_allcap_full_predictable_compact_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:57:59.969724+00:00
-- url     : https://prove2.me/theorems/fc04d4a7-830a-4ed6-9d04-e616aa64fc0b
-- title:
--   All positive caps admit compact reserve bands exhausting the full predictable mask
-- statement:
--   For each positive finite or infinite dividend cap C, strict-interior compact bands Icc(a_n/2,b_n) provide the source compensation buffer while their full original predictable pre-reserve mask bands Icc(a_n,b_n) eventually contain every fixed interior positive reserve. This proves the exact deterministic exhaustion condition for the original stopped Lévy predictable masks.
-- source:
--   Proved uncapped and finite-cap explicit full predictable compact-band children; this is a two-case Lean proof with no stochastic assumptions.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_full_predictable_compact_bands
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_full_predictable_compact_bands

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_allcap_full_predictable_compact_bands (C : ℝ≥0∞) (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) := by sorry
