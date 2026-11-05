-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_negative_zero_uniform_value_bound
-- name    : AvramDividend.Classical.avram_p3_bv_original_negative_zero_uniform_value_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:55:25.106861+00:00
-- url     : https://prove2.me/theorems/334b4bdf-ea07-4b43-81b7-f683a8b2c224
-- title:
--   Automatically bound a continuous BV verification function on every left-unbounded finite reserve strip
-- statement:
--   A verification value function w that is continuous on nonnegative reserves and identically zero at strictly negative reserves has a finite nonnegative uniform absolute-value bound on every left-unbounded finite strip (-infinity,b]. This removes the independent hWbound assumption in original-process compact compensated-jump interfaces without requiring another stochastic process.
-- source:
--   Compactness of [0,b], continuity of |w|, and vanishing of w on (-infinity,0).

import Mathlib
open Set

theorem AvramDividend.Classical.avram_p3_bv_original_negative_zero_uniform_value_bound
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v : ℝ, v ≤ b → |w v| ≤ R := by sorry
