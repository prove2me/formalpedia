-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
-- name    : AvramDividend.Classical.avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T18:18:29.215995+00:00
-- url     : https://prove2.me/theorems/ce296561-a7a6-4f20-ba40-83123be97045
-- title:
--   Nonzero negative jump measure: exact original physical finite-activity Poisson Laplace transform at positive time and tilt
-- statement:
--   For a finite-negative-activity spectrally negative Levy process with genuinely nonzero Levy jump measure, identify the positive-time positive-tilt Laplace transform of the actual physical jump sum with the negative-mark Poisson Laplace exponent on the unchanged original Omega and P. This is the difficult nonzero-jump case after the empty-jump case is handled from the proved original no-jump theorem.
-- source:
--   Original marked jump point process finite-activity Poisson exponential functional; source Proposition 4(i) and finite negative activity Levy-Ito decomposition. Existing A20 original Borel count Poisson law and proved A88 physical finite product, A85 integrability, A89/A90 original void intensities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by sorry
