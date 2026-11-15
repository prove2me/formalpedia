-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a72_original_physical_negative_jump_total_exact_laplace_20261114
-- name    : AvramDividend.Classical.avram_a72_original_physical_negative_jump_total_exact_laplace_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:06:19.504193+00:00
-- url     : https://prove2.me/theorems/3d90d56c-3a6b-4ebc-b258-6d778bc1e0f4
-- title:
--   Original finite-activity physical marked jump total has exact compound Poisson Laplace exponent at positive tilt
-- statement:
--   Original finite-activity physical marked jump total has exact compound Poisson Laplace exponent at positive tilt. Use the identical original spectrally negative Levy source, original raw filtration and physical Gaussian residual and causal jump total representatives. This is a genuine stochastic child required for A70 and A65, not an algebraic replacement.
-- source:
--   Original finite-activity Poisson marked-jump Laplace functional on the same source; source s-finite physical jump kernel, original negative jump compensator and original finite negative ν. May build on bounded-mark Poisson Laplace and monotone convergence; no Gaussian companion or independent Gaussian assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a72_original_physical_negative_jump_total_exact_laplace_20261114
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
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) * X.ψ θ -
        θ * ((t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) -
        (t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)) := by sorry
