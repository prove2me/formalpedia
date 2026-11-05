-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_C1_positive_cap_compact_band_lipschitz
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_compact_band_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:35:25.499203+00:00
-- url     : https://prove2.me/theorems/7031054f-a288-4759-8137-41b925015fd4
-- title:
--   Actual BV verification C1 positive-cap interior yields compact negative-jump Lipschitz envelope
-- statement:
--   Precisely the original C1 smoothness hypothesis from P3 bounded-variation dividend verification implies an available uniform Lipschitz constant on each positive compact reserve interval whose right endpoint lies below the cap. This supplies the local BV nonlinear source mark estimate without an additional arbitrary regularity hypothesis.
-- source:
--   Original P3 C1 positive-cap interior hypothesis and Mathlib compact convex C1 Lipschitz theorem

import Mathlib
open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_compact_band_lipschitz (w : ℝ → ℝ) (C : ℝ≥0∞) (hw : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : ENNReal.ofReal b < C) : ∃ K : ℝ≥0, LipschitzOnWith K w (Icc a b) := by sorry
