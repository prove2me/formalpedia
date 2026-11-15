-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a107_original_physical_negative_jump_exponential_expectation_unit_bound_20261114
-- name    : AvramDividend.Classical.avram_a107_original_physical_negative_jump_exponential_expectation_unit_bound_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:58:21.583188+00:00
-- url     : https://prove2.me/theorems/0fcfdd6f-b0c1-484d-b229-8433d67a102d
-- title:
--   Original finite-activity negative-jump exponential Laplace expectation is bounded above by one
-- statement:
--   For an original spectrally negative Levy process with finite negative jump mass and any nonnegative tilt, the expectation of the exponential of its actual cumulative physical negative jump sum, using any measurable almost-surely equal representative, is at most one. No zero-Gaussian, mark iid or Poisson jump law assumption is used.
-- source:
--   Proved A85 original physical negative jump exponential is integrable and pointwise in (0,1] almost everywhere, followed by monotonicity of Lebesgue integrals on the original probability measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a107_original_physical_negative_jump_exponential_expectation_unit_bound_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    (∫ ω, Real.exp (θ * J ω) ∂P) ≤ 1 := by sorry
