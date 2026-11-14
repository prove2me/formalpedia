-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_multivariate_stein_linear_gaussian
-- name    : AppliedSDE.SarkkaSolin.multivariate_stein_linear_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:45:07.142853+00:00
-- url     : https://prove2.me/theorems/7e05d419-c581-4873-ac95-3d211ca96dbd
-- title:
--   General-mean, general-covariance multivariate Gaussian Stein identity
-- statement:
--   Särkkä and Solin (2019), Theorem 9.2 and equation (9.10), printed p. 167. Let X=μ+LZ be a finite-dimensional Gaussian vector with arbitrary mean μ, standard independent Gaussian coordinates Z and covariance P=LLᵀ, allowing singular positive-semidefinite P. For a continuously differentiable bounded vector-valued function with bounded first derivative, each (i,j) component satisfies E[f_i(X)(X_j−μ_j)]=Σ_k L_jk E[D f_i(X)(L e_k)]. Together these coordinate identities constitute the complete matrix Stein Gaussian integration-by-parts formula in the textbook.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathbb E[f_i(X)(X_j-\mu_j)]=\sum_k L_{jk}\mathbb E[Df_i(X)(Le_k)]
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 9.2 and eq (9.10), printed p. 167. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.multivariate_stein_linear_gaussian
    {n m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ : Fin n → ℝ)
    (f : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (t : ℝ)
    (hf : ∀ i : Fin n, ContDiff ℝ 1 (fun x : Fin n → ℝ => f t x i))
    (hfb : ∃ C : ℝ, ∀ (x : Fin n → ℝ) (i : Fin n), |f t x i| ≤ C)
    (hfdb : ∃ D : ℝ, ∀ (x : Fin n → ℝ) (i : Fin n),
      ‖fderiv ℝ (fun y : Fin n → ℝ => f t y i) x‖ ≤ D)
    (i j : Fin n) :
    (∫ z : Fin m → ℝ, f t (μ + L z) i * (L z) j
      ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))) =
      ∑ k : Fin m, (L (Pi.single k (1 : ℝ))) j *
        (∫ z : Fin m → ℝ,
          fderiv ℝ (fun y : Fin n → ℝ => f t y i) (μ + L z)
            (L (Pi.single k (1 : ℝ)))
          ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))) := by
  sorry
