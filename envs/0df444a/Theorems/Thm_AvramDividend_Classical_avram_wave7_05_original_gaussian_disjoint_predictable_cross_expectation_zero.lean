-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:25:15.202718+00:00
-- url     : https://prove2.me/theorems/aaae4beb-33be-4deb-91ee-34eba3ba2082
-- title:
--   Two disjoint original Gaussian predictable L2 cells have exact zero covariance
-- statement:
--   For the actual original zero-jump spectrally negative Lévy source X, two disjoint deterministic source increments with 𝓕.rightCont u-measurable predictable weights, each genuinely in L2, have integrable product and exact zero real expectation. It is the source-filtration cross-isometry building block for finite Gaussian Itô grid sums, valid at σ=0 and without an independent Brownian space.
-- source:
--   W7-05 original-source corollary of Proved 0978c1ba-692c-4360-a496-9987fb45f377 and pinned integral_condExp (𝓕.rightCont.le u).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_predictable_L2_bilinear_cross_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
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
    Integrable (A * B) P ∧ (∫ ω, A ω * B ω ∂P) = 0 := by sorry
