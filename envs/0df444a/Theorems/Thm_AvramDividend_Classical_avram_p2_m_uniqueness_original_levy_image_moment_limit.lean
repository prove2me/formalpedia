-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_levy_image_moment_limit
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_moment_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:15:06.411071+00:00
-- url     : https://prove2.me/theorems/89f64039-d761-49ad-a2c8-d74576cb0d19
-- title:
--   Actual original Lévy weighted exponential image uniquely identifies all compact-test moment limits
-- statement:
--   For the true SpectrallyNegativeLevy source X with exact X.nu, any finite unit-supported candidate limit rho whose ENNReal moments match the convergent moments of the genuine time-normalised fourth-weighted exponential laws agrees on all compact interior continuous tests with the genuine negative Lévy weighted exponential image. The proof derives positivity, finite moments, and the actual moment limit from independently Proved P2-I and P2-K original-source declarations and invokes P2-M two-limit uniqueness. It does not assume any intrinsic jump-count rate or extension to arbitrary Borel marks. The NeBot right-neighbourhood filter premise makes limit uniqueness explicit.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_moment_limit
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
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    (∫ z : ℝ, g z ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp)) =
      (∫ z : ℝ, g z ∂ρ) := by sorry
