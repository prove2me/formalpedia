-- Prove2me | Theorems.Thm_ErrBoundCplx_ISTA_lemma_10_error_bound
-- name    : ErrBoundCplx.ISTA.lemma_10_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:10.613107+00:00
-- url     : https://prove2.me/theorems/146b15d2-74fa-4f36-8881-61e80e37d5bb
-- title:
--   Lemma 10, (9)–(10) — on the ℓ1 ball of radius R > ‖d‖²/(2μ), f − min f ≥ 2γ_R dist²(·, S) with γ_R = 1/(4ν²(1 + μR + (R‖A‖ + ‖d‖)(4R‖A‖ + ‖d‖)))
-- statement:
--   Let $\mu > 0$, $A \in \mathbb R^{m\times n}$, $d \in \mathbb R^m$, and $f(x) = \mu\|x\|_1 + \frac12\|Ax - d\|^2$ on $\mathbb R^n$, with $S = \operatorname{argmin} f$. Let $\nu > 0$ be a Hoffman constant (Definition 1) for the pair $(M, [\tilde A^T, \tilde\mu^T]^T)$, where $M$ is the $(2^n+1)\times(n+1)$ matrix with rows $(e_i, -1)$, $e_i \in \{\pm 1\}^n$, and $(0, \dots, 0, 1)$, and $[\tilde A^T, \tilde\mu^T]^T$ has rows $(A_j, 0)$ and $(0, \dots, 0, \mu)$. Fix $R > \|d\|^2/(2\mu)$ and let $\|A\|$ be the spectral norm. Then
--   $$f(x) - \min f \ge 2\gamma_R\, \operatorname{dist}^2(x, S) \qquad \text{for all } x \in \mathbb R^n \text{ with } \|x\|_1 \le R, \qquad (9)$$
--   where
--   $$\gamma_R = \frac{1}{4\nu^2\big(1 + \mu R + (R\|A\| + \|d\|)(4R\|A\| + \|d\|)\big)}. \qquad (10)$$
--
--   This is a quadratic growth (error bound) condition with an explicit constant; it gives the KL inequality used to derive the linear complexity bound for ISTA (Theorem 25).
--
--   **Formalization Note** The paper's data vector $b$ is $d$ here. The paper writes $f(x) - f(x^*)$ for a minimizer $x^*$, which equals $f(x) - \min f$. $\nu$ is assumed strictly positive: at $\nu = 0$ the page's (10) would be $+\infty$, while Lean's $1/0 = 0$ would make the statement trivial; since any $\nu' \ge \nu$ is again a Hoffman constant, nothing is lost. The statement rests on an external result (Beck–Shtern, Lemma 2.5).
-- source:
--   arXiv:1510.08234v3, Lemma 10, pp. 11–12, (9), (10); matrices M, Ã, μ̃ and the Hoffman couple on p. 11

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_ErrBoundCplx_ISTA_Hoffman
import Definitions.Def_ErrBoundCplx_ISTA_Lasso
open BoydADMM.Prox

namespace ErrBoundCplx.ISTA

/-- arXiv:1510.08234v3, Lemma 10, (9)–(10), pp. 11–12 (error bound for the ℓ1-regularized least
squares objective). Let `μ > 0`, `A ∈ ℝ^{m×n}`, `d ∈ ℝ^m` (the page's `b`),
`f(x) = μ‖x‖₁ + ½‖Ax − d‖²`, `S = argmin f`, and let `ν > 0` be a Hoffman constant
(Definition 1) for the couple `(M, [Ãᵀ, μ̃ᵀ]ᵀ)` of p. 11. Fix `R > ‖d‖²/(2μ)`. Then for every
`x` with `‖x‖₁ ≤ R`, `f(x) − min f ≥ 2γ_R dist²(x, S)` with
`γ_R = 1 / (4ν²(1 + μR + (R‖A‖ + ‖d‖)(4R‖A‖ + ‖d‖)))`, `‖A‖` the spectral norm. -/
theorem lemma_10_error_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ) (hμ : 0 < μ)
    (ν : ℝ) (hν : 0 < ν) (hHoff : IsHoffmanConst (hoffmanM n) (hoffmanE A μ) ν)
    (R : ℝ) (hR : ‖d‖ ^ 2 / (2 * μ) < R) :
    let γR : ℝ := 1 / (4 * ν ^ 2 *
      (1 + μ * R + (R * specNorm A + ‖d‖) * (4 * R * specNorm A + ‖d‖)))
    ∀ x : EuclideanSpace ℝ (Fin n), l1Norm x ≤ R →
      2 * γR * Metric.infDist x (lassoArgmin A d μ) ^ 2 ≤ lassoObj A d μ x - lassoMin A d μ := by sorry

end ErrBoundCplx.ISTA
