-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_physical_negative_mark_poisson_moment_model
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_physical_negative_mark_poisson_moment_model
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:47:15.175958+00:00
-- url     : https://prove2.me/theorems/9262691d-11a7-48ca-881f-aa0d9f9f2cf7
-- title:
--   Physical stopped negative-jump Poisson count and exponential marked-moment witness
-- statement:
--   Construct an actual same-space Poisson count and a global marked-exponential moment witness from the original negative-jump series of a finite-activity spectrally negative Levy process; identify r*(m-1) with the actual negative-jump Levy measure Laplace exponent. This is the outstanding physical stochastic source, without assuming the desired Laplace identity.
-- source:
--   Exact Avram original physical negative-mark jump Laplace target f4b58008-0b90-457b-b302-a1d4aa180f90. This Open theorem asks for physical Poisson extraction and marked-moment matching.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_physical_negative_mark_poisson_moment_model
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    ∃ (N : Ω → ℕ) (r : ℝ≥0) (m : ℝ),
      HasLaw N (poissonMeasure r) P ∧
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        ∫ ω, m ^ (N ω) ∂P ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) := by sorry
