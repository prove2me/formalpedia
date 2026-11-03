-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_offdiagonal_row_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_predictable_offdiagonal_row_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:46:55.155958+00:00
-- url     : https://prove2.me/theorems/fb1a7249-038c-4e6d-b367-b8efdab3f50b
-- title:
--   Original finite disjoint Gaussian predictable grid has zero off-diagonal covariance row
-- statement:
--   For each cell of a finite pairwise-separated predictable Gaussian source grid on exactly the original Levy probability space, the finite sum of cross products with all distinct other cells is integrable and has expectation zero. This is the off-diagonal cancellation step for the finite stochastic integral L2 isometry, including sigma zero.
-- source:
--   Direct corollary of Proved W7-05 exact original-source pairwise cross mean-zero 93c3a7cc-3ba0-43ef-b6fc-4eedd0a8de0e and pinned Mathlib integrable_finset_sum, integral_finset_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_predictable_offdiagonal_row_mean_zero
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
    ∀ i ∈ S,
      Integrable (fun ω => ∑ j ∈ S.erase i, F i ω * F j ω) P ∧
      (∫ ω, ∑ j ∈ S.erase i, F i ω * F j ω ∂P) = 0 := by sorry
