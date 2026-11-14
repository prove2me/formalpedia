-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_covariance_kernel_sum_and_product_psd
-- name    : AppliedSDE.SarkkaSolin.covariance_kernel_sum_and_product_psd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:45:37.970202+00:00
-- url     : https://prove2.me/theorems/b6242618-faa3-4536-bb4a-624ae8b2b201
-- title:
--   Positive semidefinite covariance kernels are closed under sums and products
-- statement:
--   Let C1 and C2 be symmetric real covariance kernels, each positive semidefinite on every finite time grid. Their pointwise sum and pointwise product are symmetric positive-semidefinite covariance kernels. This is the mathematical covariance-validity prerequisite for the book's sum and product state-space constructions (Algorithms 12.9 and 12.10). The stronger correspondence with stacked and Kronecker-sum linear SDE models is a distinct formalisation obligation.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   C_1,C_2\succeq0\ \Longrightarrow\ C_1+C_2\succeq0,\quad C_1\odot C_2\succeq0
--   $$
-- source:
--   Original derived from Särkkä and Solin, Applied Stochastic Differential Equations (2019), Section 12.3 and Algorithms 12.9–12.10, printed pp. 264–265. https://doi.org/10.1017/9781108186735

import Mathlib
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.covariance_kernel_sum_and_product_psd
    (C₁ C₂ : ℝ → ℝ → ℝ)
    (hsym₁ : ∀ s t : ℝ, C₁ s t = C₁ t s)
    (hsym₂ : ∀ s t : ℝ, C₂ s t = C₂ t s)
    (hpsd₁ : ∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * C₁ (t i) (t j))
    (hpsd₂ : ∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * C₂ (t i) (t j)) :
    (∀ s t : ℝ, C₁ s t + C₂ s t = C₁ t s + C₂ t s) ∧
    (∀ s t : ℝ, C₁ s t * C₂ s t = C₁ t s * C₂ t s) ∧
    (∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (C₁ (t i) (t j) + C₂ (t i) (t j))) ∧
    (∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (C₁ (t i) (t j) * C₂ (t i) (t j))) := by
  sorry
