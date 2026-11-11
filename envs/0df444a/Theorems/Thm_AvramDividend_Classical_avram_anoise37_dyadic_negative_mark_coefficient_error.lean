-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise37_dyadic_negative_mark_coefficient_error
-- name    : AvramDividend.Classical.avram_anoise37_dyadic_negative_mark_coefficient_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:13:47.607477+00:00
-- url     : https://prove2.me/theorems/fa09a0a9-c163-42b3-9664-81c5fe69b759
-- title:
--   Dyadic negative-mark left-coefficient has inverse-mesh pointwise error
-- statement:
--   For an original dyadic negative-mark partition cell, its left endpoint differs from each mark in that cell by at most the cell width 2⁻ᵏ, and the coefficient has absolute value at most one when the index lies in range. This is the deterministic inequality used to dominate and converge the physical signed marked-count sums in the active original-source leaf ebfd1029.
-- source:
--   Necessary deterministic dyadic coefficient estimate for public Open ebfd1029 and 5f7ea99e, with exact strict-right cell convention.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise37_dyadic_negative_mark_coefficient_error
    (k i : ℕ) (z : ℝ)
    (hi : i < 2 ^ k)
    (hz : z ∈ Set.Ioc
      (-1 + (i : ℝ) / (2 : ℝ) ^ k)
      (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)) :
    |(-1 + (i : ℝ) / (2 : ℝ) ^ k) - z| ≤
      1 / (2 : ℝ) ^ k ∧
    |(-1 + (i : ℝ) / (2 : ℝ) ^ k)| ≤ 1 := by sorry
