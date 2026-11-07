-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_full_predictable_compact_bands
-- name    : AvramDividend.Classical.avram_bv_meas7_finite_full_predictable_compact_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:53:29.828359+00:00
-- url     : https://prove2.me/theorems/c2deb232-405a-4587-a061-d7c29b64c6dd
-- title:
--   Original finite-cap full predictable reserve bands exhaust every strict interior reserve
-- statement:
--   For every positive finite dividend cap C, choose the explicit strict-interior compact bands a_n=min(1,C.toReal/2)/(n+1) and b_n=C.toReal(n+1)/(n+2). Each full predictable mask band Icc(a_n,b_n) eventually contains every fixed positive strict-interior reserve, while its buffer Icc(a_n/2,b_n) remains inside the cap. This bridges exact previsible stopped Lévy compensator masks and finite-cap interior exhaustion.
-- source:
--   Kernel-checked finite-cap geometry from proved source 204ef2ef, with the stronger proved finite full-band eventual reserve inclusion BV-MEAS7 theorem.

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_full_predictable_band_eventually_contains_reserve

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_finite_full_predictable_compact_bands (C : ℝ≥0∞) (hC : 0 < C) (hTop : C ≠ ⊤) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) := by sorry
