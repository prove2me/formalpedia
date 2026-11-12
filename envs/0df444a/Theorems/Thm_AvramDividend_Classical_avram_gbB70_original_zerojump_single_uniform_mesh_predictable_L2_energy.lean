-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB70_original_zerojump_single_uniform_mesh_predictable_L2_energy
-- name    : AvramDividend.Classical.avram_gbB70_original_zerojump_single_uniform_mesh_predictable_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:53:48.376992+00:00
-- url     : https://prove2.me/theorems/53d82ea6-867e-4fd2-adb2-76b1d793553c
-- title:
--   Original no-jump Gaussian bounded predictable coefficients satisfy a single-grid L² energy bound
-- statement:
--   For arbitrary uniformly bounded predictable coefficients on a single deterministic uniform mesh of the original zero-jump Lévy process and right-continuous filtration, the drift-centred finite sum is square-integrable and its squared expectation is nonnegative and bounded by the original Gaussian variance times the cell width and the sum of coefficient second moments. This is the genuine one-grid stochastic isometry input for the already Proved two-grid deterministic refinement identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB70_original_zerojump_single_uniform_mesh_predictable_L2_energy
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
      let L : Ω → ℝ := fun ω =>
        (Finset.range N).sum (fun i =>
          H i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
            (Δ : ℝ) * X.c))
      0 ≤ (∫ ω, (L ω) ^ 2 ∂P) ∧
        (∫ ω, (L ω) ^ 2 ∂P) ≤
          X.σ ^ 2 * ((n : ℝ) / (N : ℝ)) *
            (Finset.range N).sum (fun i =>
              ∫ ω, (H i ω) ^ 2 ∂P) := by sorry
