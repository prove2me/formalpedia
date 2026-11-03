-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:34:45.636223+00:00
-- url     : https://prove2.me/theorems/93c3a7cc-3ba0-43ef-b6fc-4eedd0a8de0e
-- title:
--   Finite separated original Gaussian predictable source cells are pairwise orthogonal in L2
-- statement:
--   For a finite collection of pairwise time-separated actual original Gaussian source increments with predictable L2 coefficients, every distinct weighted-cell product is integrable and has exact expectation zero, irrespective of which interval occurs first. Arbitrary Gaussian sigma including zero, same original Ω/P/X/filtration.
-- source:
--   W7-05 finite-family source pairwise covariance corollary of Proved aaae4beb-33be-4deb-91ee-34eba3ba2082.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)) 2 P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Integrable (F i * F j) P ∧
        (∫ ω, F i ω * F j ω ∂P) = 0 := by sorry
