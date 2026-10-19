-- Prove2me | Theorems.Thm_ApproxSparseHDSL_ExcessRisk_proposition_2
-- name    : ApproxSparseHDSL.ExcessRisk.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:13.151585+00:00
-- url     : https://prove2.me/theorems/c8a79846-2c6e-4b2d-b596-1a01277531d4
-- title:
--   Proposition 2, p. ec20 — an S³ONC solution has no entry with |β̂ⱼ| ∈ (0, aλ), almost surely
-- statement:
--   Let the data $Z_1, \dots, Z_n$, the loss $L$ and the smoothness constant $U_L$ of (11) be as in the model, and let $a, \lambda > 0$ be the MCP parameters with $a < U_L^{-1}$. Let $\hat\beta$ be a random vector in $\mathbb R^p$ with $\|\hat\beta\|_\infty \le R$ almost surely that satisfies the S³ONC$(Z_1^n)$ almost surely. Then
--
--   $$
--   \mathbb P\big[\,|\hat\beta_j| \notin (0, a\lambda) \text{ for all } j\,\big] = 1.
--   $$
--
--   The second-order part of the S³ONC therefore forces every coordinate of an S³ONC solution to be either zero or at least $a\lambda$ in magnitude; this is what makes the penalty term of such a solution proportional to its sparsity.
--
--   **Formalization Note** "Probability one" is stated as an almost-everywhere statement. $\hat\beta$ is any measurable map $\Omega \to \mathbb R^p$; the theorem does not construct it.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, p. ec20, Proposition 2

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- Proposition 2, p. ec20: if `a < 1/U_L` and the random vector `β̂` lies in the box
`‖β̂‖∞ ≤ R` and satisfies the S³ONC almost surely, then almost surely no coordinate of `β̂`
has `|β̂ⱼ| ∈ (0, aλ)`. -/
theorem proposition_2 {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure E) {p n : ℕ} (Z : Fin n → Ω → E)
    (L : (Fin p → ℝ) → E → ℝ) (UL R a lam : ℝ) (betaHat : Ω → Fin p → ℝ)
    (hS : IIDSample P μ Z L) (h11 : Smooth11 μ L UL)
    (ha : 0 < a) (hlam : 0 < lam) (haUL : a < 1 / UL)
    (hmeas : Measurable betaHat) (hbox : ∀ᵐ ω ∂P, InBox R (betaHat ω))
    (hS3 : ∀ᵐ ω ∂P, S3ONC UL a lam L (sample Z ω) (betaHat ω)) :
    ∀ᵐ ω ∂P, ∀ j, |betaHat ω j| ∉ Set.Ioo 0 (a * lam) := by sorry

end ApproxSparseHDSL.ExcessRisk
