-- Prove2me | Theorems.Thm_CVPricing_Regret_design_matrix_eigenvalue_bounds
-- name    : CVPricing.Regret.design_matrix_eigenvalue_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:31:39.797101+00:00
-- url     : https://prove2.me/theorems/9ca511cd-ef92-451d-aa51-996406e514c6
-- title:
--   Lemma 1 — λ_max(t) ≤ (1 + p_h²) t and t Var(p)_t ≤ (1 + p_h²) λ_min(t)
-- statement:
--   Let $0 < p_l < p_h$, $t \ge 2$, and prices $p_1, \dots, p_t \in [p_l, p_h]$ with $p_1 \ne p_2$. Let $\lambda_{\max}(t)$ and $\lambda_{\min}(t)$ be the largest and smallest eigenvalues of the design matrix
--
--   $$P_t = \begin{pmatrix} t & \sum_{i=1}^t p_i \\ \sum_{i=1}^t p_i & \sum_{i=1}^t p_i^2 \end{pmatrix}.$$
--
--   Then
--
--   $$\lambda_{\max}(t) \le (1 + p_h^2)\, t \qquad \text{and} \qquad t \operatorname{Var}(p)_t \le (1 + p_h^2)\, \lambda_{\min}(t).$$
--
--   The lemma converts the variance bound of Proposition 2 into a lower bound on the information in the data, which is the form the consistency results for quasi-likelihood estimates require.
--
--   **Formalization Note** $\lambda_{\max}$ and $\lambda_{\min}$ of the symmetric matrix $P_t$ are written as the maximum and minimum of $y^\top P_t y$ over Euclidean unit vectors $y \in \mathbb R^2$ (Rayleigh–Ritz). $P_t$ is `fisherOf p t` and $t\operatorname{Var}(p)_t$ is `infoMetricOf p t` from the referenced Keskin–Zeevi definitions.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 776 (PDF 8), Lemma 1

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares

open Matrix KeskinZeevi.SufficientConditions

namespace CVPricing.Regret

/-- Lemma 1 (den Boer–Zwart 2014, p. 776): for prices `p₁, …, p_t ∈ [pl, ph]` (`0 < pl < ph`),
`t ≥ 2`, `p₁ ≠ p₂`, the design matrix `P_t = Σ_{i=1}^t (1, p_i)ᵀ(1, p_i)` (`fisherOf p t`) has
largest eigenvalue `λ_max(t) ≤ (1 + ph²) t` and smallest eigenvalue with
`t Var(p)_t ≤ (1 + ph²) λ_min(t)` (`infoMetricOf p t = t Var(p)_t`). The extreme eigenvalues of the
symmetric matrix `P_t` are written as the maximum and minimum of the Rayleigh quotient
`yᵀ P_t y` over Euclidean unit vectors. -/
theorem design_matrix_eigenvalue_bounds (pl ph : ℝ) (hpl : 0 < pl) (hlh : pl < ph)
    (p : ℕ → ℝ) (t : ℕ) (ht : 2 ≤ t) (hp : ∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc pl ph)
    (h12 : p 1 ≠ p 2) :
    (⨆ y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1}, y.1 ⬝ᵥ (fisherOf p t *ᵥ y.1))
        ≤ (1 + ph ^ 2) * t ∧
      infoMetricOf p t ≤ (1 + ph ^ 2) * minRayleigh (fisherOf p t) := by sorry

end CVPricing.Regret
