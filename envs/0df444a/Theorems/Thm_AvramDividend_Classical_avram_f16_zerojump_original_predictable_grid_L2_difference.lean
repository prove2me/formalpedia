-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f16_zerojump_original_predictable_grid_L2_difference
-- name    : AvramDividend.Classical.avram_f16_zerojump_original_predictable_grid_L2_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:05:52.751741+00:00
-- url     : https://prove2.me/theorems/d06aa80a-379d-400c-a81f-8a71d18ec8bd
-- title:
--   Original zero-jump Lévy predictable simple-integral grid difference obeys exact L² isometry
-- statement:
--   On the exact original Lévy probability space with ν=0, two predictable finite-grid integrands G,H have a square-integrable difference stochastic sum and an exact sum-of-cell-variances identity, assuming each physical cell weighted innovation lies in L². Obtained by instantiating the Proved all-triplet same-path Gaussian simple-integral isometry with Y=X and zero jump paths. This supplies an acyclic quantitative Cauchy mesh tool for the original stopped Gaussian HJB proof.
-- source:
--   Source-exact zero-jump specialisation of Proved eb689476-244d-4098-86d9-c68735ddeebb with X=Y, no alternate space, no nonphysical Brownian copy. Needed to establish finite-grid L² Cauchy limits for a029846e but does not assume or claim pathwise Ito source convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_predictable_simple_integral_difference_L2
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f16_zerojump_original_predictable_grid_L2_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
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
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      (G i ω - H i ω) *
        ((X.X (t i) ω - (t i : ℝ) * X.c) -
         (X.X (s i) ω - (s i : ℝ) * X.c))) 2 P) :
    let V : ι → Ω → ℝ := fun i ω =>
      (X.X (t i) ω - (t i : ℝ) * X.c) -
      (X.X (s i) ω - (s i : ℝ) * X.c)
    let SG : Ω → ℝ := fun ω => ∑ i ∈ S, G i ω * V i ω
    let SH : Ω → ℝ := fun ω => ∑ i ∈ S, H i ω * V i ω
    MemLp (fun ω => SG ω - SH ω) 2 P ∧
    Integrable (fun ω => (SG ω - SH ω) ^ 2) P ∧
    (∫ ω, (SG ω - SH ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, ((G i ω - H i ω) * V i ω) ^ 2 ∂P) := by sorry
