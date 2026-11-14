-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_stein_affine_coordinate
-- name    : AppliedSDE.SarkkaSolin.gaussian_stein_affine_coordinate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:00:21.6362+00:00
-- url     : https://prove2.me/theorems/891bdbde-0849-4b73-ac71-6731f74b4a3a
-- title:
--   Affine Gaussian integration by parts for one standard-coordinate direction
-- statement:
--   For a bounded continuously differentiable scalar test function g on a finite real vector space, with globally bounded first derivative, and a finite-dimensional continuous real-linear map L, the Gaussian Stein integration by parts identity holds for every independent standard Gaussian coordinate k after adding any fixed mean μ. This is a direct affine translation of the published Proved HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts theorem. Its conclusion equates the expectation of Z_k g(μ+LZ) and the directional derivative expectation; no Stein identity is assumed as a hypothesis. This is the per-coordinate ingredient for the open Applied SDE Chapter 9 multivariate Gaussian Stein identity 7e05d419-c581-4873-ac95-3d211ca96dbd.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 9, Gaussian assumed-density integration by parts; https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.gaussian_stein_affine_coordinate
    {n m : ℕ}
    (L : (Fin (m + 1) → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g)
    (hgb : ∃ C : ℝ, ∀ x : Fin n → ℝ, |g x| ≤ C)
    (hgdb : ∃ D : ℝ, ∀ x : Fin n → ℝ, ‖fderiv ℝ g x‖ ≤ D)
    (k : Fin (m + 1)) :
    (∫ z : Fin (m + 1) → ℝ, z k * g (μ + L z)
      ∂(Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))) =
    ∫ z : Fin (m + 1) → ℝ,
      fderiv ℝ g (μ + L z) (L (Pi.single k (1 : ℝ)))
      ∂(Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1)) := by
  sorry
