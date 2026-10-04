-- Prove2me | Theorems.Thm_Cohen2019_Robust_prob_X_A
-- name    : Cohen2019.Robust.prob_X_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:03:27.584505+00:00
-- url     : https://prove2.me/theorems/4d985e88-48fd-4012-99e8-c92641e73dc5
-- title:
--   Appendix A.0.1, Claim — $\mathbb P(X \in A) = \underline{p_A}$
-- statement:
--   Let $\sigma > 0$, $x \in \mathbb R^d$, $\delta \in \mathbb R^d$ with $\delta \neq 0$, $X \sim \mathcal N(x, \sigma^2 I)$, and $0 < \underline{p_A} < 1$. Let
--   $$
--   A = \{z \in \mathbb R^d : \delta^\top (z - x) \le \sigma \|\delta\|\, \Phi^{-1}(\underline{p_A})\}.
--   $$
--   Then
--   $$
--   \mathbb P(X \in A) = \underline{p_A}.
--   $$
--
--   The half-space $A$ is the region on which the "worst-case" base classifier of the proof of Theorem 1 predicts $c_A$; this claim says that this classifier is consistent with the lower bound $\underline{p_A}$ on the probability of $c_A$ at $x$.
--
--   **Formalization Note** $\Phi^{-1}$ is the real inverse of the standard Gaussian CDF on $(0,1)$. The hypotheses $\delta \neq 0$ and $0 < \underline{p_A} < 1$ are implicit in the paper's computation (it divides by $\|\delta\|$ and uses $\Phi(\Phi^{-1}(p)) = p$); for $\delta = 0$ the set $A$ is all of $\mathbb R^d$ or empty.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Appendix A.0.1, Claim P(X ∈ A) = p̲A, p. 15; A defined in the proof of Theorem 1, p. 14 (PDF pages)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Claim `ℙ(X ∈ A) = p̲A`.** Cohen, Rosenfeld, Kolter, *Certified Adversarial Robustness via
Randomized Smoothing*, arXiv:1902.02918v2, Appendix A.0.1, p. 15; the half-space
`A := {z : δᵀ(z − x) ≤ σ‖δ‖Φ⁻¹(p̲A)}` is defined in the proof of Theorem 1, p. 14 (PDF pages).

**Formalization Note.** `X ∼ 𝒩(x, σ²I)` is `gaussNoise x σ`, `Y ∼ 𝒩(x + δ, σ²I)` is
`gaussNoise (x + δ) σ`, `δᵀv` is `inner ℝ δ v`, `Φ⁻¹` is the real inverse `PhiInvReal` on `(0, 1)`.
The hypotheses `δ ≠ 0` and `0 < p < 1` are added: they are implicit in the paper's computation
(it divides by `‖δ‖` and uses `Φ(Φ⁻¹(p)) = p`); at `δ = 0` the half-space is all of `ℝᵈ` or empty
and the identity fails, and in Theorem 1 the case `δ = 0` and the endpoint probabilities are
handled separately. -/
theorem prob_X_A {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d)) (hδ : δ ≠ 0)
    (pA : ℝ) (hpA0 : 0 < pA) (hpA1 : pA < 1) :
    (gaussNoise x σ {z | inner ℝ δ (z - x) ≤ σ * ‖δ‖ * PhiInvReal pA}).toReal = pA := by sorry

end Cohen2019.Robust
