-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
-- name    : AvramDividend.Classical.avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:20:19.333279+00:00
-- url     : https://prove2.me/theorems/5f5c5c86-c0cf-4a5f-a141-fbf4140053f4
-- title:
--   Exact real Ioc-cell right-dyadic kernel is finite Stieltjes step sum
-- statement:
--   For T>0 and 0<s≤T, the full finite Stieltjes step function on the real half-open cells (iT/N,(i+1)T/N] is precisely the value at the upward ceiling endpoint ceil(sN/T). The equality is pointwise for arbitrary ENNReal weights, so full random Stieltjes mass is preserved in integration.
-- source:
--   Accepted ceiling-index cell sum helper and ordered-field equivalences of half-open scaled time intervals.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_cell_indicator_sum_eq_ceiling
open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
    (T s : ℝ) (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range N,
      if s ∈ Ioc ((i : ℝ) * T / (N : ℝ))
        (((i + 1 : ℕ) : ℝ) * T / (N : ℝ))
      then a (i + 1) else 0) =
    a (Nat.ceil ((s / T) * (N : ℝ))) := by sorry
