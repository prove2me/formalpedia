-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_levy_positive_band_moment_limit
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_positive_band_moment_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:25:17.983566+00:00
-- url     : https://prove2.me/theorems/fce1f9ee-ed42-4f21-8aaa-891c02c7475f
-- title:
--   Actual negative Lévy image is unique for positive-band moment limits
-- statement:
--   For the actual spectrally negative Lévy source X with exact X.nu and fourth-weighted exp image, any finite unit-supported candidate moment limit rho whose monomial integrals are limits of the real-time normalised original-process image agrees with the actual X.nu image on continuous positive-band tests vanishing near zero and at or above one. Such a test may have irrelevant nonzero negative-argument Real.log values. All actual-source positivity, finiteness and moment convergence premises are discharged by Proved P2-I/P2-K helpers; rho moment convergence is explicit. The proof uses independently proved positive-band two-limit uniqueness without assuming original marked-count intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_positive_band_moment_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Measure ℝ)
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hunit_ρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1)
    (hfinite_ρ : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ) ≠ ⊤)
    (hmom_ρ : ∀ k, Tendsto (fun h : ℝ =>
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ •
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
         else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    (∫ z : ℝ, g z ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp)) =
      (∫ z : ℝ, g z ∂ρ) := by sorry
