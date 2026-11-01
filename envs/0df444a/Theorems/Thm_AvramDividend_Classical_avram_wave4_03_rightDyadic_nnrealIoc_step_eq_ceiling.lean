-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_nnrealIoc_step_eq_ceiling
-- name    : AvramDividend.Classical.avram_wave4_03_rightDyadic_nnrealIoc_step_eq_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:30:49.45254+00:00
-- url     : https://prove2.me/theorems/51601be5-79d9-416e-938b-e540008699ab
-- title:
--   Actual NNReal clock right-dyadic Ioc mesh indicator equals exact ceiling kernel
-- statement:
--   For a genuine nonnegative time T, each time 0<s≤T selects exactly its right dyadic Ioc cell on the NNReal mesh used by the original filtered Lévy process, and the ENNReal step sum equals the ceiling-indexed value. This matches the proof's exact NNReal dyadic kernel, not a surrogate grid.
-- source:
--   Proved real grid Ioc indicator identity plus coercions ℝ≥0→ℝ and powers. Necessary to join original-source full Stieltjes double Fatou to actual finite-grid expected budget.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_rightDyadic_nnrealIoc_step_eq_ceiling
    (T s : ℝ≥0) (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T)
    (n : ℕ) (a : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range (2 ^ n),
      if (s : ℝ) ∈ Ioc
        (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ)
        (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ)
      then a (i + 1) else 0) =
    a (Nat.ceil (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)) := by sorry
