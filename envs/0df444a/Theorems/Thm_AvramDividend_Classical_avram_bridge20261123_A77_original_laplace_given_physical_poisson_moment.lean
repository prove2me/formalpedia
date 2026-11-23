-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_laplace_given_physical_poisson_moment
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_laplace_given_physical_poisson_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:47:13.287329+00:00
-- url     : https://prove2.me/theorems/f44a8d2d-938b-4640-9557-2babb1ae524e
-- title:
--   Original negative-jump Laplace transform from a genuine same-space Poisson marked-moment certificate
-- statement:
--   Use the source-Proved compound-Poisson Laplace transform identity to recover the exact original negative-jump stochastic Laplace transform from a same-space count-law and marked-moment identity. The physical model is an explicit added assumption, whose construction remains an Open source theorem.
-- source:
--   Exact original target f4b58008-0b90-457b-b302-a1d4aa180f90 and the public Proved abstract Poisson Laplace theorem 585fcae9-d5a6-4b40-800f-10e7e744aa81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_laplace_given_physical_poisson_moment
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
        else 0)
    (hModel :
    ∃ (N : Ω → ℕ) (r : ℝ≥0) (m : ℝ),
      HasLaw N (poissonMeasure r) P ∧
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        ∫ ω, m ^ (N ω) ∂P ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by sorry
