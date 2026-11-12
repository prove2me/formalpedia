-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger168_clipped_discount_counterterm_sum_partition
-- name    : AvramDividend.Classical.avram_gledger168_clipped_discount_counterterm_sum_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:55:35.651837+00:00
-- url     : https://prove2.me/theorems/45b7d6b8-9ccd-4294-a67d-b9eeed3cb9be
-- title:
--   Chronological discount counterterm stops before the final index
-- statement:
--   Finite deterministic partition of the shorter stopped discount Riemann counterterm. The crossing term is present only when its index is strictly less than the last index; correct at zero and final boundary. Necessary second half of gledger166 and gledger164.
-- source:
--   Original uniform stopped grid and exact counterterm range m.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger168_clipped_discount_counterterm_sum_partition
    (n m : ℕ) (ρ : ℝ≥0) (q : ℝ) (W : ℕ → ℝ) (k : ℕ)
    (hk : k ≤ m)
    (hlo : ∀ i : ℕ, i ≤ k →
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) < ρ)
    (hhi : ∀ i : ℕ, k < i →
      ρ ≤ ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    (∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ then q * (Δ : ℝ) * E s * W i else 0) =
      (∑ i ∈ Finset.range k,
        q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ) * W i) +
      (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) * W k else 0) := by sorry
