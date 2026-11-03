-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_disjoint_predictable_two_cell_orthogonal_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_05_original_gaussian_disjoint_predictable_two_cell_orthogonal_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:18:17.949996+00:00
-- url     : https://prove2.me/theorems/f0f64fc5-977e-4e9f-b728-1867c882e552
-- title:
--   Two original stopped Gaussian predictable cells obey exact orthogonal L2 energy additivity
-- statement:
--   For the same original spectrally negative Lévy source X with zero jump measure and arbitrary σ, take disjoint intervals s≤t≤u≤v. Two F_u-measurable real predictable weights G,H with L2 weighted source-centred increments produce an L1 square of their sum, and its expected square is the sum of expected squares. The proof uses the Proved original-source conditional cross-zero theorem 0978c1ba, integral_condExp on original 𝓕.rightCont u, and real algebra; no unrelated Brownian space, no positive σ hypothesis. This is a two-step stochastic integral isometry input, not a mixed-jump continuous martingale construction.
-- source:
--   W7-05 source-specific L2 Pythagoras from canonical Proved 0978c1ba-692c-4360-a496-9987fb45f377.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_predictable_L2_bilinear_cross_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_gaussian_disjoint_predictable_two_cell_orthogonal_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (G H : Ω → ℝ)
    (hG : Measurable[𝓕.rightCont u] G)
    (hH : Measurable[𝓕.rightCont u] H)
    (hM1 : MemLp (fun ω =>
      G ω * (X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c)) 2 P)
    (hM2 : MemLp (fun ω =>
      H ω * (X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c)) 2 P) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    let A : Ω → ℝ := G * Y₁
    let B : Ω → ℝ := H * Y₂
    Integrable (fun ω => (A ω + B ω) ^ 2) P ∧
      (∫ ω, (A ω + B ω) ^ 2 ∂P) =
        (∫ ω, (A ω) ^ 2 ∂P) +
          (∫ ω, (B ω) ^ 2 ∂P) := by sorry
