-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_expanding_compact_bands
-- name    : AvramDividend.Classical.avram_p3_grid4_finite_cap_expanding_compact_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:24:16.42774+00:00
-- url     : https://prove2.me/theorems/204ef2ef-a823-4fb1-90e4-e4180cf0c9d4
-- title:
--   Explicit nested strict-interior compact bands for every original finite dividend cap
-- statement:
--   For every strictly positive finite cap C, construct explicit positive lower and cap-strict upper bands satisfying all the geometric hypotheses of the Proved original indexed compensated Levy signed-source budget 6d66798c. The witnesses a_n=min(1,C.toReal/2)/(n+1), b_n=C.toReal(n+1)/(n+2) move towards the entire strict reserve interior. No stochastic budget or stopped physical-grid identity is asserted here.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_finite_cap_expanding_compact_bands
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C ≠ ⊤) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by sorry
