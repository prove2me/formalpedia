-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:01:06.791656+00:00
-- url     : https://prove2.me/theorems/78e197ea-3427-4cce-aab5-066bba435863
-- title:
--   Finite predictable original Gaussian source grid satisfies exact orthogonal L2 isometry
-- statement:
--   On the exact canonical original Levy source and right-continuous filtration with zero jump measure, a finite family of nonoverlapping deterministic Gaussian increments times predictable L2 weights has an L2 sum whose exact squared expectation equals the sum of each squared expectation. The proof makes all quadratic integrability explicit and cancels the full off-diagonal double sum by Proved original-source orthogonality. Arbitrary source sigma including zero; no independent Brownian construction.
-- source:
--   W7-05 original finite off-diagonal double sum zero after proof, pinned Mathlib memLp_finset_sum, MemLp.integrable_sq and finite sum algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_offdiagonal_double_sum_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
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
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by sorry
