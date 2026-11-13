-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB197_original_one_mesh_gaussian_L2_isometry_from_bounded_predictable
-- name    : AvramDividend.Classical.avram_gbB197_original_one_mesh_gaussian_L2_isometry_from_bounded_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:00:31.293873+00:00
-- url     : https://prove2.me/theorems/cafa34b1-1dc6-4cc5-86ee-7f06932f6c2d
-- title:
--   Bounded predictable source Gaussian uniform-grid linear L2 equals physical time coefficient energy
-- statement:
--   For the original Gaussian zero-jump process and globally bounded coefficients measurable at their sampled right-continuous filtration times, the finite one-grid linear centred Gaussian sum has second moment equal to Gaussian variance times the original step coefficient time-square energy.
-- source:
--   Avram Gaussian B original process; Proved B79 Gaussian offdiagonal grid, B80 Gaussian same-cell covariance, B196 deterministic one-grid step-square time integration. Intended generic core for B66.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB197_original_one_mesh_gaussian_L2_isometry_from_bounded_predictable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n m : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hAdapt : ∀ (k i : ℕ), Measurable[𝓕.rightCont
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))] (G k i))
    (hStrong : ∀ k i, StronglyMeasurable (G k i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ k i ω, |G k i ω| ≤ B) :
    let L : ℕ → Ω → ℝ := fun k ω =>
      let δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
      (Finset.range (k + 1)).sum (fun i =>
        G k i ω * (X.X (s i + δ) ω -
          X.X (s i) ω - (δ : ℝ) * X.c))
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    (∫ ω, (L m ω) ^ 2 ∂P) =
      X.σ ^ 2 * (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K m t ω) ^ 2 ∂P) ∂volume) := by sorry
