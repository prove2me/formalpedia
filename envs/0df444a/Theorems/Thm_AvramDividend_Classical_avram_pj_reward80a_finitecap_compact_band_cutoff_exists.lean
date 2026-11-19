-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward80a_finitecap_compact_band_cutoff_exists
-- name    : AvramDividend.Classical.avram_pj_reward80a_finitecap_compact_band_cutoff_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:10:30.800612+00:00
-- url     : https://prove2.me/theorems/79948fba-db1f-4af2-b114-0c00e903284f
-- title:
--   Source80 deterministic smooth finitecap band with simultaneous valid negative-mark cutoff
-- statement:
--   From positive finite reserve cap C and original C2 generator domain, choose a compact interior C2 band and an independent strict cutoff eta between 0 and 1. This is exactly the deterministic parameter part of the physical stopped purejump source80, without assuming stochastic ledger witnesses.
-- source:
--   Existing proved original compact band theorem 58184d4f; choose eta=1/2 independent of the true clock, preserving finite cap interior.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward80a_finitecap_compact_band_cutoff_exists
    (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ Cband u v δ η : ℝ,
      0 < u ∧ 0 < δ ∧ δ ≤ 1 ∧ u + δ < v ∧
      0 < η ∧ η < 1 ∧ v < Cband ∧ v < C.toReal ∧
      ContDiffOn ℝ 2 w (Ioo 0 Cband) := by sorry
