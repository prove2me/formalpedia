-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger173_discount_coe_exact_real_partition_normalization
-- name    : AvramDividend.Classical.avram_gledger173_discount_coe_exact_real_partition_normalization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:31:01.269919+00:00
-- url     : https://prove2.me/theorems/e7b5b0f8-7725-4716-b809-bfe5731e941c
-- title:
--   Exact real-coercion normalization of original clipped discount partition
-- statement:
--   A purely definitional equality converting the already Proved exact clipped NNReal chronological partition into the corresponding real-time exponential formula needed by Proved aggregation and boundary inequalities. It handles the exact rho terminal displacement and the conditional missing final Riemann term. This reduction makes the remaining gledger164 proof small enough for strict proof complexity limits, with no additional stochastic assumptions.
-- source:
--   Pinned NNReal coercion algebra and exact mesh successor equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger173_discount_coe_exact_real_partition_normalization
    (m k : ℕ) (ρ Δ : ℝ≥0) (q : ℝ) (W : ℕ → ℝ) :
    let E : ℝ≥0 → ℝ := fun u => Real.exp (-(q * (u : ℝ)))
    let s : ℕ → ℝ := fun i => (((i : ℝ≥0) * Δ : ℝ≥0) : ℝ)
    let t : ℝ := (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ)
    let r : ℝ := (ρ : ℝ) - t
    (∑ i ∈ Finset.range k,
      (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ) +
        q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ)) * W i) +
    (E ρ - E ((k : ℝ≥0) * Δ) +
      (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) else 0)) * W k =
    (∑ i ∈ Finset.range k,
      (Real.exp (-(q * (s i + (Δ : ℝ)))) -
        Real.exp (-(q * s i)) +
        q * (Δ : ℝ) * Real.exp (-(q * s i))) * W i) +
    (Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
      (if k < m then q * (Δ : ℝ) * Real.exp (-(q * t)) else 0)) * W k := by sorry
