-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva79_original_supplied_uniform_physical_clock_strict_step
-- name    : AvramDividend.Classical.avram_bva79_original_supplied_uniform_physical_clock_strict_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:07:22.7136+00:00
-- url     : https://prove2.me/theorems/412d0490-8f00-46ad-81bd-7dc680a53b25
-- title:
--   Every cell in the supplied original BV physical uniform grid is strictly increasing
-- statement:
--   For the actual ℝ≥0 grid supplied to original bounded-variation infinite-activity BV source problems, its exact real formula u(n,i)=T*i/(n+2) with positive T ensures every successive clock strictly increases. This source-level property supplies disjoint positively oriented cells for the stopped cash Stieltjes and compensated negative jump grid; no replacement grid is chosen.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva79_original_supplied_uniform_physical_clock_strict_step
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n i : ℕ, u n i < u n (i + 1) := by sorry
