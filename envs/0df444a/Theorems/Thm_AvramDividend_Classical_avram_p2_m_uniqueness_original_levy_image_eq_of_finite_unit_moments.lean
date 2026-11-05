-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_levy_image_eq_of_finite_unit_moments
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_eq_of_finite_unit_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:44:00.763506+00:00
-- url     : https://prove2.me/theorems/f45f9d69-4883-44fb-948c-c10604de3451
-- title:
--   Original Levy weighted image equality from finite unit-supported candidate moments alone
-- statement:
--   Remove three redundant analytic hypotheses from the already Proved original source Borel image uniqueness theorem. For finite regular original and candidate image measures, source image identity and candidate support on [0,1], genuine all-k original-process normalised fourth-weighted moment convergence forces equality on every Borel set. The high ENNReal moments are bounded by total mass, and real monomials are automatically integrable by the two Proved P2-I helpers. This has the exact original X.X and X.ν conventions and strict negative-mark cutoff. It leaves independent candidate moment convergence, source measure finiteness/regularity and the actual Borel-rate inverse for P2-B and P2-A.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_eq_of_finite_unit_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (η ρ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ] [η.Regular] [ρ.Regular]
    (hη : η = (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hunit_ρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1)
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
