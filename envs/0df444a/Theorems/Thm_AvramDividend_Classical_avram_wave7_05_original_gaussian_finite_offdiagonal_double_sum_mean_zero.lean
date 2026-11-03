-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_offdiagonal_double_sum_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_offdiagonal_double_sum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:47:06.592143+00:00
-- url     : https://prove2.me/theorems/8af1b137-c04c-4260-8efa-dcbe398c449f
-- title:
--   All off-diagonal finite source Gaussian predictable grid covariance cancels exactly
-- statement:
--   For any finite grid of pairwise-separated original zero-jump Levy Gaussian source increments, predictably weighted in the original right-continuous filtration and genuinely in L2, every off-diagonal covariance is integrable and the whole double sum of cross products is integrable with zero expectation. This cancellation is a necessary finite-step Gaussian stochastic integral isometry term; sigma can be zero.
-- source:
--   Proved W7-05 original finite-family pairwise orthogonality 93c3a7cc-3ba0-43ef-b6fc-4eedd0a8de0e and pinned finite-sum integrability/integral interchange.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_offdiagonal_double_sum_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
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
    Integrable (fun ω =>
      ∑ i ∈ S, ∑ j ∈ S.erase i, F i ω * F j ω) P ∧
    (∫ ω, ∑ i ∈ S, ∑ j ∈ S.erase i, F i ω * F j ω ∂P) = 0 := by sorry
