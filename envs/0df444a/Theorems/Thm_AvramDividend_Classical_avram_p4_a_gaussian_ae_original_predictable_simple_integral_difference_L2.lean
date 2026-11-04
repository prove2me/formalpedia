-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_predictable_simple_integral_difference_L2
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_predictable_simple_integral_difference_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:32:50.3345+00:00
-- url     : https://prove2.me/theorems/eb689476-244d-4098-86d9-c68735ddeebb
-- title:
--   Original Gaussian predictable simple stochastic integral L2 difference exact orthogonality
-- statement:
--   For two same-grid predictable step integrands G and H of the original jump-bearing Levy X Gaussian residual, assuming source a.s. all-times extraction and explicitly L2 cell errors, the difference of their finite simple stochastic integrals belongs to L2 with exactly the sum of disjoint cell square errors. A bridge to proving Cauchy convergence of approximations; no completed integral or bracket asserted.
-- source:
--   Proved P4-A original-X finite predictable grid L2 isometry 3e0fcecf-cfb9-4b43-b87e-43c9c379f6a1; linearity of finite sum and a.e. MemLp transport.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_finite_grid_exact_L2_isometry
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_predictable_simple_integral_difference_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (s t : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hHown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (H i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hHpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (H i))
    (hLp : ∀ i ∈ S, MemLp (fun ω => (G i ω - H i ω) *
      ((X.X (t i) ω - (t i : ℝ) * X.c - Jsmall (t i) ω - Jlarge (t i) ω) -
       (X.X (s i) ω - (s i : ℝ) * X.c - Jsmall (s i) ω - Jlarge (s i) ω))) 2 P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (t i) ω - (t i : ℝ) * X.c -
        Jsmall (t i) ω - Jlarge (t i) ω) -
      (X.X (s i) ω - (s i : ℝ) * X.c -
        Jsmall (s i) ω - Jlarge (s i) ω)
    let SG : Ω → ℝ := fun ω => ∑ i ∈ S, G i ω * M i ω
    let SH : Ω → ℝ := fun ω => ∑ i ∈ S, H i ω * M i ω
    MemLp (fun ω => SG ω - SH ω) 2 P ∧
    Integrable (fun ω => (SG ω - SH ω) ^ 2) P ∧
    (∫ ω, (SG ω - SH ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, ((G i ω - H i ω) * M i ω) ^ 2 ∂P) := by sorry
