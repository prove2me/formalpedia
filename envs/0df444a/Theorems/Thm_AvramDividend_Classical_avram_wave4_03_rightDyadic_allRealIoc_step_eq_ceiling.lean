-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
-- name    : AvramDividend.Classical.avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:42:38.294993+00:00
-- url     : https://prove2.me/theorems/3f4cb787-bb09-4491-bc0d-3baf0e78a4e9
-- title:
--   Whole real-time original dyadic Stieltjes step exactly equals right-ceiling kernel
-- statement:
--   On the actual NNReal dyadic time grid with T>0, the complete ENNReal sum of real Ioc-cell indicators equals the right-ceiling value on 0<s≤T and vanishes elsewhere. Valid for every real time s and arbitrary nonnegative weights, hence exact inside full Stieltjes integrals without atom concentration.
-- source:
--   Positive-time exact source clock dyadic indicator-ceiling identity plus upper mesh point ≤T on every finite cell.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
    (T : ℝ≥0) (hT : 0 < T) (s : ℝ)
    (n : ℕ) (a : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range (2 ^ n),
      if s ∈ Ioc
        (((i : ℝ≥0) / (2 : ℝ≥0) ^ n) * T : ℝ)
        (((((i + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) : ℝ)
      then a (i + 1) else 0) =
    if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      a (Nat.ceil (((s.toNNReal / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n))
    else 0 := by sorry
