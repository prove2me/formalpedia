-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a70_original_gaussian_physical_jump_independence_marginal_20261114
-- name    : AvramDividend.Classical.avram_a70_original_gaussian_physical_jump_independence_marginal_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T12:58:28.471063+00:00
-- url     : https://prove2.me/theorems/04becb8b-a744-4759-b552-1a112595b5b0
-- title:
--   Original Gaussian residual and finite negative physical marked jump total are independent, with exact jump marginal Laplace
-- statement:
--   Isolate the genuine same-Omega/P finite-activity Levy-Ito marked Poisson theorem: for a measurable residual/jump pair H,J equal almost everywhere to the actual physical Gaussian residual and the actual jump sum and satisfying the source decomposition everywhere, the positive-tilt exponentials of H and J are independent, and J has the exact compound-Poisson Laplace marginal. The required compensated drift and sigma-square cancellation are packaged into the explicit exponent. This is the irreducible probabilistic source gap remaining after Proved A68 measurable pair, A69 drift-shifted source Laplace, A66 physical sign and A67 bounded jump exponential.
-- source:
--   Lévy-Ito finite activity decomposition on the original filtration, original source s-finite jump kernel Proved eb357d08, Proved physical source jump sum identity 6366b3de, actual finite jump support 12644677, X.laplace and source Poisson factorisation. This theorem does not assume a Gaussian companion and is acyclic relative to A65.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a70_original_gaussian_physical_jump_independence_marginal_20261114
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
      (fun ω => Real.exp (θ * J ω)) P ∧
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) * X.ψ θ -
        θ * ((t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) -
        (t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)) := by sorry
