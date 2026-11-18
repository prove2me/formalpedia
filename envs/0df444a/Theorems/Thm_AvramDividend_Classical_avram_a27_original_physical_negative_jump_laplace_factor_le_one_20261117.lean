-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:03:35.876516+00:00
-- url     : https://prove2.me/theorems/3d3367bc-d9f1-47d2-97f2-cfa41727eb2b
-- title:
--   Actual original negative physical jump exponential weight is in the positive unit interval
-- statement:
--   For the exact original finite-activity physical negative jump sum and nonnegative tilt theta, the marked jump Laplace weight exp(theta J_t) is strictly positive and at most one almost surely. This provides a uniform dominated bound for source Poisson-cell generating functions and mesh limits.
-- source:
--   Proved original finite physical negative-jump exponential product a88 and source spectrally-negative jump sign wave4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual negative-mark Laplace factor is strictly positive and at most one. -/

theorem AvramDividend.Classical.avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    ∀ᵐ ω ∂P,
      0 < Real.exp (θ * J ω) ∧ Real.exp (θ * J ω) ≤ 1 := by sorry
