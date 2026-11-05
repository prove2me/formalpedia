-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_levy_image_borel_eq_candidate
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_borel_eq_candidate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:19:07.353058+00:00
-- url     : https://prove2.me/theorems/1d336430-429a-4bbb-8e1a-920f26f9c46c
-- title:
--   Actual original negative Levy weighted image equals any finite regular source-moment candidate on all Borel sets
-- statement:
--   For the actual spectrally negative Levy process, the true negative fourth-weighted exponential image and any competing finite regular unit-supported candidate law with genuine original X.X time-normalized monomial limits are equal as full Borel measures. The actual image monomial limits and unit support are proved by P2-K and the original negative image support theorem. The independent candidate moment limit, finite regularity and real integrability remain explicit. Apply the separately proved P2-M full ENNReal Hausdorff uniqueness theorem to equality of every moment, including total mass. No stationary marked-count intensity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_borel_eq_candidate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (η ρ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ] [η.Regular] [ρ.Regular]
    (hη : η = (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hunit_ρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1)
    (hrealη : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) η)
    (hrealρ : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) ρ)
    (hfiniteρ : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ) ≠ ⊤)
    (hmomρ : ∀ k, Tendsto (fun h : ℝ =>
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ •
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
         else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ))) :
    η = ρ := by sorry
