-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB73_original_zerojump_uniform_finite_sum_orthogonality
-- name    : AvramDividend.Classical.avram_gbB73_original_zerojump_uniform_finite_sum_orthogonality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:14:39.18987+00:00
-- url     : https://prove2.me/theorems/0401f699-692e-4a00-a8bd-8e28468db3e6
-- title:
--   Original Gaussian deterministic uniform-grid bounded predictable increments are L² orthogonal
-- statement:
--   The square expectation of a finite original zero-jump Lévy Gaussian grid sum of bounded left-history predictable weights is the sum of each physical cell square expectation. This is the off-diagonal cancellation part of single-grid isometry, built from the Proved original finite-grid predictable isometry 78e197ea, with L² membership derived from bounded weights and Gaussian cell moments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB73_original_zerojump_uniform_finite_sum_orthogonality
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
    (∫ ω, (L ω) ^ 2 ∂P) =
      (Finset.range N).sum (fun i =>
        ∫ ω, (H i ω * (X.X (s i + Δ) ω -
          X.X (s i) ω - (Δ : ℝ) * X.c)) ^ 2 ∂P) := by sorry
