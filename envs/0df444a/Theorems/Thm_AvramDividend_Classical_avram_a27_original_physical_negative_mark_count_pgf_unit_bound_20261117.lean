-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_mark_count_pgf_unit_bound_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_mark_count_pgf_unit_bound_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:29:53.021204+00:00
-- url     : https://prove2.me/theorems/08b8a34a-7c07-402a-9d4d-fa77f1368fee
-- title:
--   Actual physical negative-jump marked Poisson count PGF expectation is between zero and one
-- statement:
--   On the original finite-activity spectrally negative Lévy probability space, for every nonnegative theta and unit-interval generating argument z, the expected marked-count generating weight z^K exp(theta J) exists and lies between zero and one. This provides an original-source bound for solving the marked-Poisson generating-function Volterra equation.
-- source:
--   Proved exact original physical jump exponential bound and actual jointly integrable marked-count PGF, with elementary powers and Bochner integral domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original negative-jump marked-count PGF takes values in the unit interval. -/

theorem AvramDividend.Classical.avram_a27_original_physical_negative_mark_count_pgf_unit_bound_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ (∫ ω, z ^ K ω * Real.exp (θ * J ω) ∂P) ∧
      (∫ ω, z ^ K ω * Real.exp (θ * J ω) ∂P) ≤ 1 := by sorry
