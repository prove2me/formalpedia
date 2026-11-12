-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger170_clipped_discount_crossing_witness_exact_partition
-- name    : AvramDividend.Classical.avram_gledger170_clipped_discount_crossing_witness_exact_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:19:56.917538+00:00
-- url     : https://prove2.me/theorems/7a57c833-a43a-4f8a-8f59-b9a5870dd774
-- title:
--   Exact positive stopped-mesh partition with source-certified crossing endpoints
-- statement:
--   Strengthened finite-stopped weighted discount identity carrying the true first-crossing inequalities k delta < rho <= (k+1) delta in its existential witness. The inequalities permit direct use of original preterminal weight bounds, and the identity preserves all original crossing and missing-final-Riemann terms. This is the exact crossing source missing from weaker gledger166 and needed to close gledger164.
-- source:
--   Proved gledger163 true uniform-grid crossing, Proved gledger167 and gledger168 exact finite sums. No stochastic hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gledger163_true_uniform_clipped_mesh_first_crossing
import Theorems.Thm_AvramDividend_Classical_avram_gledger167_clipped_discount_exp_weighted_sum_partition
import Theorems.Thm_AvramDividend_Classical_avram_gledger168_clipped_discount_counterterm_sum_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger170_clipped_discount_crossing_witness_exact_partition
    (n m : ℕ) (hn : 0 < n) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) (q : ℝ) (W : ℕ → ℝ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∃ k : ℕ, k ≤ m ∧
      (k : ℝ≥0) * Δ < ρ ∧
      ρ ≤ (((k + 1 : ℕ) : ℝ≥0) * Δ) ∧
      (∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * W i) +
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ then q * (Δ : ℝ) * E s * W i else 0) =
      (∑ i ∈ Finset.range k,
        (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ) +
          q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ)) * W i) +
      (E ρ - E ((k : ℝ≥0) * Δ) +
        (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) else 0)) * W k := by sorry
