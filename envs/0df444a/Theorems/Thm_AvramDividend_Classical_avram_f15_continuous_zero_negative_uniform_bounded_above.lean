-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f15_continuous_zero_negative_uniform_bounded_above
-- name    : AvramDividend.Classical.avram_f15_continuous_zero_negative_uniform_bounded_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:35:32.033314+00:00
-- url     : https://prove2.me/theorems/631281b2-d843-49eb-a9e0-cc43cf4a414d
-- title:
--   Continuous nonnegative-side potential vanishing on negatives is bounded on upper halflines
-- statement:
--   An original potential continuous on the nonnegative halfline and zero on the negative halfline is uniformly bounded in absolute value on (-infinity,K]. Compactness reduces the positive part to [0,max(0,K)].
-- source:
--   Deterministic compactness lemma for the exact original UBV terminal value localisation.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_f15_continuous_zero_negative_uniform_bounded_above
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (K : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, y ≤ K → |w y| ≤ B := by sorry
