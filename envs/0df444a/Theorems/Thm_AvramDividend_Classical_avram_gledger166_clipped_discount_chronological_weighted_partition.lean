-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger166_clipped_discount_chronological_weighted_partition
-- name    : AvramDividend.Classical.avram_gledger166_clipped_discount_chronological_weighted_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:44:56.019947+00:00
-- url     : https://prove2.me/theorems/cecd4f95-2771-4a37-b633-00431fcff2fb
-- title:
--   Exact chronological weighted stopped discount mesh identity including missing final counterterm
-- statement:
--   A purely deterministic finite-grid equality: split the complete original uniform stopped discount first sum and its shorter Riemann counterterm at the first crossing. Every pre-crossing cell is full, every post-crossing exponential difference is zero, and the one crossing cell contains its Riemann counterterm only when the crossing index is less than the final mesh index. The exact identity is needed to apply already Proved cell and terminal bounds in gledger164. It does not involve any original process or final expectation inequality.
-- source:
--   Proved gledger163 positive stopped-clock unique first crossing with exact n/(m+1) mesh; elementary finite chronological sum splitting.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger163_true_uniform_clipped_mesh_first_crossing
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger166_clipped_discount_chronological_weighted_partition
    (n m : ℕ) (hn : 0 < n) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) (q : ℝ) (W : ℕ → ℝ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∃ k : ℕ, k ≤ m ∧
      (∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * W i) +
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ then q * (Δ : ℝ) * E s * W i else 0) =
      (∑ i ∈ Finset.range k,
        (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ) +
          q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ)) * W i) +
      (E ρ - E ((k : ℝ≥0) * Δ) +
        (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) else 0)) * W k :=
      by sorry
