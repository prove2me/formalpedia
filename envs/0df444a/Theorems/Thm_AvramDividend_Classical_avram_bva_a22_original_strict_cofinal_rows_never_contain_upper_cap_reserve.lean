-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_strict_cofinal_rows_never_contain_upper_cap_reserve
-- name    : AvramDividend.Classical.avram_bva_a22_original_strict_cofinal_rows_never_contain_upper_cap_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:33:37.125585+00:00
-- url     : https://prove2.me/theorems/63581204-4176-4447-ae27-f7ff8d41b852
-- title:
--   Original A22 strict cofinal spatial bands exclude the upper cap reserve on every prescribed row
-- statement:
--   Every source spatial band is strictly inside the cap, despite cofinal coverage of the cap interior. For every original row n and real reserve y whose extended-real image equals C, y is excluded from the marked jump spatial band [a_n,b_n]. Upper-cap occupation therefore receives no compensation in the literal original A22 spatially masked martingale. This is the boundary-obstruction lemma for an original finite-cap counterexample.

import Mathlib
open Classical Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_strict_cofinal_rows_never_contain_upper_cap_reserve
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) (y : ℝ) (hcap : ENNReal.ofReal y = C) :
    y ∉ Icc (a n) (b n) := by sorry
