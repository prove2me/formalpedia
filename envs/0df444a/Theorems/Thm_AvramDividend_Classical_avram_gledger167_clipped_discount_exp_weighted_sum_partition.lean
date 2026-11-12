-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger167_clipped_discount_exp_weighted_sum_partition
-- name    : AvramDividend.Classical.avram_gledger167_clipped_discount_exp_weighted_sum_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:55:39.81428+00:00
-- url     : https://prove2.me/theorems/ad87d1b9-148f-4da9-819a-a0ddcf85bf29
-- title:
--   Chronological stopped exponential first sum separates the unique crossing
-- statement:
--   Finite deterministic partition of the weighted clipped exponential first sum into complete interior cells and the one crossing cell, assuming exact pre/post crossing grid inequalities. Necessary first half of gledger166 and gledger164.
-- source:
--   Original uniform stopped physical grid and elementary finite sum partition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger167_clipped_discount_exp_weighted_sum_partition
    (n m : ℕ) (ρ : ℝ≥0) (q : ℝ) (W : ℕ → ℝ) (k : ℕ)
    (hk : k ≤ m)
    (hlo : ∀ i : ℕ, i ≤ k →
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) < ρ)
    (hhi : ∀ i : ℕ, k < i →
      ρ ≤ ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    (∑ i ∈ Finset.range (m + 1), (E (v (i + 1)) - E (v i)) * W i) =
      (∑ i ∈ Finset.range k,
        (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ)) * W i) +
        (E ρ - E ((k : ℝ≥0) * Δ)) * W k := by sorry
