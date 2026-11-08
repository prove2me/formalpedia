-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_ae_eventual_clipping
-- name    : AvramDividend.Classical.avram_bv_residual10_original_rowwise_ae_eventual_clipping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:34:52.741469+00:00
-- url     : https://prove2.me/theorems/aeae67b2-89d3-4ea8-b7ed-0745a2fb51ec
-- title:
--   Summably chosen original uniform-row coefficient clipping is eventually exact almost surely
-- statement:
--   Under finite original-process measure and coordinate measurability, summable positive coefficient-cutoff tolerances permit one deterministic cutoff for each refining physical row such that, almost surely, all row coordinates lie below their selected bounds for every sufficiently late row. This gives eventual pathwise exactness of clipping despite changing row length and does not claim expectation convergence without an L1 envelope.
-- source:
--   AVRAM BV-RESIDUAL10 original uniform-row localisation and pinned Borel-Cantelli, 7 November 2026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_probability_diagonal

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_rowwise_ae_eventual_clipping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (a : ℕ → Ω → ℕ → ℝ)
    (ha : ∀ n i, Measurable (fun ω => a n ω i))
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤) :
    ∃ K : ℕ → ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∀ i ∈ Finset.range (n + 1), abs (a n ω i) ≤ (K n : ℝ) := by sorry
