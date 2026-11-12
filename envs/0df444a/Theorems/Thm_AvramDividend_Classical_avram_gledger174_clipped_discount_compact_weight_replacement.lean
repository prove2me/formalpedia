-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger174_clipped_discount_compact_weight_replacement
-- name    : AvramDividend.Classical.avram_gledger174_clipped_discount_compact_weight_replacement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:45:15.33235+00:00
-- url     : https://prove2.me/theorems/dd554b1d-8b9c-4e2a-bf9f-6d2c6696bae0
-- title:
--   Exact finite clipped discount replacement of original weights by a compact measurable extension
-- statement:
--   A purely deterministic finite-clipped-mesh identity. If a compact extension H agrees with the physical weight w at every strictly pre-stopping state Y(t), replacing w with H leaves the complete first stopped exponential difference sum and shorter active Riemann counterterm unchanged. Every post-stopping first-sum coefficient is zero, including the terminal crossing. This is the remaining exact algebraic bridge for the original-source measurability gledger160; Y will be the original X minus right-limit D.
-- source:
--   Exact physical mesh / chronological identity with no stochastic assumptions, based on Proved gledger167 and gledger168 first/second sum reasoning.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger174_clipped_discount_compact_weight_replacement
    (n m : ℕ) (ρ : ℝ≥0) (q : ℝ) (w H : ℝ → ℝ)
    (Y : ℝ≥0 → ℝ)
    (hHw : ∀ t : ℝ≥0, t < ρ → H (Y t) = w (Y t)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    (∑ i ∈ Finset.range (m + 1),
      (E (v (i + 1)) - E (v i)) * H (Y (v i))) +
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ then q * (Δ : ℝ) * E s * H (Y s) else 0) =
    (∑ i ∈ Finset.range (m + 1),
      (E (v (i + 1)) - E (v i)) * w (Y (v i))) +
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ then q * (Δ : ℝ) * E s * w (Y s) else 0) := by sorry
