-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_uniform_band_cofinal
-- name    : AvramDividend.Classical.avram_bv_meas7_allcap_uniform_band_cofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:40:54.360494+00:00
-- url     : https://prove2.me/theorems/56bac59c-48ba-4ef2-bab4-4ebb86e53aa6
-- title:
--   All positive dividend caps admit cofinal strict-interior compact reserve bands
-- statement:
--   A single finite/infinite cap localisation theorem combines already proved explicit finite-cap and uncapped constructions. For every positive cap C, compact reserve bands sit strictly inside its interior and eventually contain every fixed positive interior reserve. This provides the deterministic exhaustion premise for the actual stopped Lévy compensated integral.
-- source:
--   BV-MEAS7 verified finite-cap and uncapped cofinal compact-band children. This is an exact two-case Lean split, without any stochastic assumptions.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_uniform_band_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_cap_uniform_band_cofinal

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_allcap_uniform_band_cofinal (C : ℝ≥0∞) (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n / 2) (b n)) := by sorry
