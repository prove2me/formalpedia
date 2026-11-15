-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a71_original_gaussian_physical_negative_jump_independence_20261114
-- name    : AvramDividend.Classical.avram_a71_original_gaussian_physical_negative_jump_independence_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:06:19.982858+00:00
-- url     : https://prove2.me/theorems/8374759d-8bbe-439a-92a8-8ae4258b5742
-- title:
--   Original positive-variance Gaussian residual independent of full causal marked jump total on identical probability space
-- statement:
--   Original positive-variance Gaussian residual independent of full causal marked jump total on identical probability space. Use the identical original spectrally negative Levy source, original raw filtration and physical Gaussian residual and causal jump total representatives. This is a genuine stochastic child required for A70 and A65, not an algebraic replacement.
-- source:
--   Levy-Ito finite-activity source independence of continuous Gaussian and compound Poisson negative-mark jump process, on the original completed process path representation, no auxiliary probability space; original X.indepIncrements plus actual source marked jump kernel and source Gaussian limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a71_original_gaussian_physical_negative_jump_independence_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (H J : Ω → ℝ)
    (hHMeas : Measurable H) (hJMeas : Measurable J)
    (hHEq : H =ᵐ[P] R t)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hDecomp : ∀ ω, H ω + J ω =
      X.X t ω -
        (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) :
    IndepFun (fun ω => Real.exp (θ * H ω))
      (fun ω => Real.exp (θ * J ω)) P := by sorry
