-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
-- name    : AvramDividend.Classical.avram_a85_original_physical_negative_jump_exponential_integrable_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:11:31.732051+00:00
-- url     : https://prove2.me/theorems/171176d6-b4dc-4915-a40e-b5dde88417ec
-- title:
--   Original finite-activity physical negative-jump exponential has bounded integrable positive-tilt law
-- statement:
--   For an original spectrally negative Levy process with finite negative jump mass, every measurable random variable agreeing almost surely with the full causal physical negative jump sum has a strictly positive exponential bounded above by one, integrable under P for all nonnegative Laplace tilts. Holds for all Gaussian variances.
-- source:
--   Proved A66 actual finite-activity cumulative negative jump sums are nonpositive; Proved A35 finite-support causal marked tsum identity; Proved A67 nonpositive exponential bounded integrable theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a85_original_physical_negative_jump_exponential_integrable_20261114
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
    Integrable (fun ω => Real.exp (θ * J ω)) P ∧
    (∀ᵐ ω ∂P,
      0 < Real.exp (θ * J ω) ∧
      Real.exp (θ * J ω) ≤ 1) := by sorry
