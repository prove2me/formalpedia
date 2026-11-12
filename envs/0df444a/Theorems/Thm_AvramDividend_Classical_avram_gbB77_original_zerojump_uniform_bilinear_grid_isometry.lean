-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB77_original_zerojump_uniform_bilinear_grid_isometry
-- name    : AvramDividend.Classical.avram_gbB77_original_zerojump_uniform_bilinear_grid_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:08:25.772318+00:00
-- url     : https://prove2.me/theorems/edeab944-da19-457c-bf7d-c4b04eafb724
-- title:
--   Original Gaussian one-grid exact bilinear covariance for two bounded predictable coefficient fields
-- statement:
--   For two bounded predictable coefficient fields on the same deterministic grid in the original zero-jump Lévy process, expected product of their centred finite grid gains equals sigma squared times the grid cell width multiplied by the sum of expected coefficient products. Derive by polarising the Proved original-source finite-grid orthogonality and exact diagonal variance identities.
-- source:
--   True root-connected stochastic atom for the generic two-grid covariance gbB76; its adaptation to common uniform product refinements is deterministic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB77_original_zerojump_uniform_bilinear_grid_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H J : ℕ → Ω → ℝ)
    (hHAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont
      ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hJAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont
      ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (J i))
    (hHBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B)
    (hJBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |J i ω| ≤ B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let L : (ℕ → Ω → ℝ) → Ω → ℝ := fun W ω =>
      (Finset.range N).sum (fun i =>
        W i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
          (Δ : ℝ) * X.c))
    (∫ ω, L H ω * L J ω ∂P) =
      ((Δ : ℝ) * X.σ ^ 2) *
        (Finset.range N).sum (fun i => ∫ ω, H i ω * J i ω ∂P) := by sorry
