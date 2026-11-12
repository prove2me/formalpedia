-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB76_original_two_uniform_grid_generic_predictable_covariance
-- name    : AvramDividend.Classical.avram_gbB76_original_two_uniform_grid_generic_predictable_covariance
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T16:51:27.909241+00:00
-- url     : https://prove2.me/theorems/7ece0bf6-3cd7-482d-8b53-e67db47cbce8
-- title:
--   Original Gaussian generic two uniform-grid bounded predictable coefficient covariance
-- statement:
--   For two arbitrary deterministic uniform meshes and bounded coefficients measurable at their own original right-continuous filtration left endpoints, their centred original-Gaussian grid sums have exact bilinear covariance given by sigma squared times the space-time coefficient product energy. This is the generic stochastic core of the finite-cap controlled-reserve theorem gbB67.
-- source:
--   Root-connected replacement child of gbB67: combine product common-refinement telescoping with original predictable Gaussian finite-grid isometry and bilinear cell covariance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB76_original_two_uniform_grid_generic_predictable_covariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hAdapt : ∀ (m i : ℕ),
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))]
        (G m i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ m i ω, |G m i ω| ≤ B) :
    let L : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        G m i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
          (Δ : ℝ) * X.c))
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    ∀ m l,
      (∫ ω, (L m ω) * (L l ω) ∂P) =
        X.σ ^ 2 *
          (∫ t in Ioo (0 : ℝ) (n : ℝ),
            (∫ ω, (K m t ω) * (K l t ω) ∂P) ∂volume) := by sorry
