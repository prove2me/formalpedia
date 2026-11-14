-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
-- name    : AvramDividend.Classical.avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T10:16:46.452457+00:00
-- url     : https://prove2.me/theorems/0a3377d0-fbdc-4ef3-b1cb-2564de03001c
-- title:
--   Stochastic occupation-time representation for nondegenerate Gaussian martingale plus locally finite-variation correction
-- statement:
--   For the given genuine continuous Gaussian-bracket martingale and an arbitrary locally finite-variation correction, construct almost surely a nonnegative locally bounded compactly supported spatial density whose integrals represent exact stopped physical-time occupation in every open spatial interval. The density can be càdlàg in its spatial argument and incorporates the reciprocal Gaussian quadratic-variation coefficient. Proving this requires a sound stochastic Tanaka or semimartingale occupation-time formula and cannot be assumed from existing deterministic compactness results.
-- source:
--   Major analytic bottleneck from B227 to original fixed-level B100 then B65: true semimartingale Tanaka/local-time construction for original source with FV dividends, no synthetic Brownian assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
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
