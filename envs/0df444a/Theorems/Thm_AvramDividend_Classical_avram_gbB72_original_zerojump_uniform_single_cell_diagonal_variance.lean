-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB72_original_zerojump_uniform_single_cell_diagonal_variance
-- name    : AvramDividend.Classical.avram_gbB72_original_zerojump_uniform_single_cell_diagonal_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:14:28.343214+00:00
-- url     : https://prove2.me/theorems/3ca32271-928e-44e4-891d-e65f0d8a8613
-- title:
--   Original no-jump Gaussian single predictable uniform-cell variance equals sigma squared times coefficient energy
-- statement:
--   For each original deterministic Gaussian cell, a bounded coefficient measurable at the actual original right-continuous filtration at its left endpoint has exactly the source Gaussian increment variance times its second moment. This is the diagonal part of single-grid isometry, available from the Proved stopped-history original-source bracket theorem 4294d18f once constant-clock measurability is transported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB72_original_zerojump_uniform_single_cell_diagonal_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H : ℕ → Ω → ℝ)
    (hAdapt : ∀ i : ℕ,
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    ∀ i : ℕ,
      (∫ ω, (H i ω * (X.X (s i + Δ) ω -
        X.X (s i) ω - (Δ : ℝ) * X.c)) ^ 2 ∂P) =
      (∫ ω, (H i ω) ^ 2 ∂P) * ((Δ : ℝ) * X.σ ^ 2) := by sorry
