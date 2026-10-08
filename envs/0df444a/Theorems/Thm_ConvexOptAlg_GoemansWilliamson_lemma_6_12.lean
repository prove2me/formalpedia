-- Prove2me | Theorems.Thm_ConvexOptAlg_GoemansWilliamson_lemma_6_12
-- name    : ConvexOptAlg.GoemansWilliamson.lemma_6_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:22:03.208667+00:00
-- url     : https://prove2.me/theorems/31bc9d3c-9f29-46f7-9b23-3b874a19c943
-- title:
--   Lemma 6.12, p. 345 — for ξ ∼ N(0, Σ) with unit diagonal and ζ = sign(ξ), E ζ_iζ_j = (2/π) arcsin(Σ_ij)
-- statement:
--   Let $\Sigma\in\mathbb R^{n\times n}$ be symmetric positive semidefinite with $\Sigma_{i,i}=1$ for every $i\in[n]$. Let $\xi\sim\mathcal N(0,\Sigma)$ be a centered Gaussian vector in $\mathbb R^n$ with covariance matrix $\Sigma$, and let $\zeta=\operatorname{sign}(\xi)\in\{-1,1\}^n$. Then for all $i,j\in[n]$, $\zeta_i\zeta_j$ is integrable and
--
--   $$\mathbb E\,\zeta_i\zeta_j=\frac{2}{\pi}\arcsin(\Sigma_{i,j}).$$
--
--   This is Sheppard's formula for the correlation of the signs of two jointly Gaussian variables with unit variances; it computes the expected value of the Goemans–Williamson rounding term by term.
--
--   **Formalization Note** $\mathcal N(0,\Sigma)$ is Mathlib's `multivariateGaussian 0 Σ` on `EuclideanSpace ℝ (Fin n)`, the image of the standard Gaussian under $\Sigma^{1/2}$; it is defined for singular $\Sigma$ as well. Positive semidefiniteness of $\Sigma$ is implicit in the book ("$\xi\sim\mathcal N(0,\Sigma)$": $\Sigma$ is a covariance matrix) and is stated as a hypothesis, since Mathlib's construction returns the Dirac mass at $0$ for a non-PSD matrix. The sign takes the value $1$ at $0$. Integrability of the bounded integrand is part of the conclusion.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 6.12, p. 345

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

namespace ConvexOptAlg.GoemansWilliamson

open MeasureTheory ProbabilityTheory

/-- **Lemma 6.12** (Bubeck, arXiv:1405.4980v2, §6.6, p. 345). Let `ξ ∼ N(0, Σ)` with `Σ i i = 1`
for `i ∈ [n]`, and `ζ = sign(ξ)`. Then `E ζᵢζⱼ = (2/π) arcsin(Σ i j)`.

`N(0, Σ)` is Mathlib's `multivariateGaussian 0 Σ` on `EuclideanSpace ℝ (Fin n)` (the centered
Gaussian with covariance matrix `Σ`, defined for every positive semidefinite `Σ`, singular or
not); `Σ` positive semidefinite is implicit in the book (it is a covariance matrix). The sign
takes values in `{−1, 1}` (`sgn 0 = 1`). The integrand is bounded and measurable; its
integrability is asserted as part of the conclusion. -/
theorem lemma_6_12 {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ) (hpsd : Sig.PosSemidef)
    (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => sgn (ξ i) * sgn (ξ j))
        (multivariateGaussian 0 Sig) ∧
      ∫ ξ, sgn (ξ i) * sgn (ξ j) ∂(multivariateGaussian 0 Sig) =
        2 / Real.pi * Real.arcsin (Sig i j) := by sorry

end ConvexOptAlg.GoemansWilliamson
