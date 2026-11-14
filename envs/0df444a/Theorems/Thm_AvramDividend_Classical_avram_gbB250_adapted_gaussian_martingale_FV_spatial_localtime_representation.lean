-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB250_adapted_gaussian_martingale_FV_spatial_localtime_representation
-- name    : AvramDividend.Classical.avram_gbB250_adapted_gaussian_martingale_FV_spatial_localtime_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T11:33:36.827296+00:00
-- url     : https://prove2.me/theorems/cd6eb515-78e7-46e2-918c-36c554a49544
-- title:
--   Adapted càdlàg finite-variation correction of nondegenerate Gaussian martingale has locally bounded spatial occupation density
-- statement:
--   For the original Gaussian-bracket continuous martingale and a right-continuous, adapted locally bounded-variation dividend correction, establish the stopped semimartingale occupation-time representation by a nonnegative locally bounded compactly supported spatial local-time density. The extra adaptedness and right-continuity assumptions are genuinely proved for original rightLimit dividends, so this is an applicable semimartingale route rather than the stronger arbitrary possibly anticipative BV perturbation statement B243.
-- source:
--   Classical Tanaka-Meyer and occupation-time formula for adapted right-continuous finite-variation semimartingale control; source https://arxiv.org/html/1802.09679v1. Original adaptation/right-continuity proved 18945919 and bba8dbb3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB250_adapted_gaussian_martingale_FV_spatial_localtime_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (Xsrc : ℝ≥0 → Ω → ℝ) (c σ : ℝ) (hσ : 0 < σ)
    (hM : Martingale (fun t ω =>
      Xsrc t ω - (t : ℝ) * c) 𝓕 P)
    (hQ : Martingale (fun t ω =>
      (Xsrc t ω - (t : ℝ) * c) ^ 2 -
      (t : ℝ) * σ ^ 2) 𝓕 P)
    (hContinuous : ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ≥0 => Xsrc t ω))
    (Dsrc : ℝ≥0 → Ω → ℝ)
    (hFV : ∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => Dsrc t ω) Set.univ)
    (hDAdapt : Adapted 𝓕 Dsrc)
    (hDright : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 => Dsrc s ω)
        (Set.Ici t) t)
    (x : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ R : ℝ, ∃ ℓ : ℝ → ℝ,
      (∀ z, 0 ≤ ℓ z) ∧
      (∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0) ∧
      (∀ z, ∃ U ∈ 𝓝 z, Bornology.IsBounded (ℓ '' U)) ∧
      (∀ a b : ℝ,
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          x + Xsrc (Real.toNNReal t) ω -
            Dsrc (Real.toNNReal t) ω ∈ Set.Ioo a b} =
        ∫⁻ z in Set.Ioo a b, ENNReal.ofReal (ℓ z) ∂volume) := by sorry
