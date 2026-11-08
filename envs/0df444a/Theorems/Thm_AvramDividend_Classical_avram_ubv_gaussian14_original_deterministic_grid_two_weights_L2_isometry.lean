-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_original_deterministic_grid_two_weights_L2_isometry
-- name    : AvramDividend.Classical.avram_ubv_gaussian14_original_deterministic_grid_two_weights_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:47:26.936694+00:00
-- url     : https://prove2.me/theorems/2ea831f9-262d-415f-8565-c76a2f2604f0
-- title:
--   Original Gaussian deterministic-grid two-integrand difference has exact L² isometry
-- statement:
--   Given two original-filtration predictable coefficients on the identical finite deterministic disjoint grid, the difference of their original no-jump Lévy Gaussian source sums is square integrable, and its exact squared expectation equals the sum of the squared per-cell coefficient-difference terms. Establishing Cauchy in terminal L² now reduces to bounding this explicit original energy as coefficients refine. The original Gaussian source and filtration are unchanged.
-- source:
--   Proved original Gaussian predictable finite-grid exact L2 isometry 78e197ea, specialised to coefficient difference G-H and finset sum linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian14_original_deterministic_grid_two_weights_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (s t : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hHown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (H i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hHpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (H i))
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      (G i ω - H i ω) * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)) 2 P) :
    let d : ι → Ω → ℝ := fun i ω =>
      X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
    let QG : Ω → ℝ := fun ω => ∑ i ∈ S, G i ω * d i ω
    let QH : Ω → ℝ := fun ω => ∑ i ∈ S, H i ω * d i ω
    MemLp (QG - QH) 2 P ∧
      Integrable (fun ω => (QG ω - QH ω) ^ 2) P ∧
      (∫ ω, (QG ω - QH ω) ^ 2 ∂P) =
        ∑ i ∈ S, (∫ ω, ((G i ω - H i ω) * d i ω) ^ 2 ∂P) := by sorry
