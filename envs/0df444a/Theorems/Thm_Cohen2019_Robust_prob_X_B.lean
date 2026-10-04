-- Prove2me | Theorems.Thm_Cohen2019_Robust_prob_X_B
-- name    : Cohen2019.Robust.prob_X_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:03:34.248183+00:00
-- url     : https://prove2.me/theorems/a5ca7779-cfc9-4a67-9f9f-e8b7dbb60026
-- title:
--   Appendix A.0.1, Claim — $\mathbb P(X \in B) = \overline{p_B}$
-- statement:
--   Let $\sigma > 0$, $x \in \mathbb R^d$, $\delta \in \mathbb R^d$ with $\delta \neq 0$, $X \sim \mathcal N(x, \sigma^2 I)$, and $0 < \overline{p_B} < 1$. Let
--   $$
--   B = \{z \in \mathbb R^d : \delta^\top (z - x) \ge \sigma \|\delta\|\, \Phi^{-1}(1 - \overline{p_B})\}.
--   $$
--   Then
--   $$
--   \mathbb P(X \in B) = \overline{p_B}.
--   $$
--
--   The half-space $B$ is where the "worst-case" classifier of the proof of Theorem 1 predicts the runner-up class; the claim says that it is consistent with the upper bound $\overline{p_B}$.
--
--   **Formalization Note** $\Phi^{-1}$ is the real inverse of the standard Gaussian CDF on $(0,1)$. The hypotheses $\delta \neq 0$ and $0 < \overline{p_B} < 1$ are implicit in the paper's computation. The paper's proof of this claim misprints the set with "$\le$" and its first line as $\mathbb P(X \in A)$; the definition of $B$ on p. 14 (with "$\ge$") is used.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Appendix A.0.1, Claim P(X ∈ B) = p̄B, p. 15; B defined in the proof of Theorem 1, p. 14 (PDF pages)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Claim `ℙ(X ∈ B) = p̄B`.** Cohen, Rosenfeld, Kolter, *Certified Adversarial Robustness via
Randomized Smoothing*, arXiv:1902.02918v2, Appendix A.0.1, p. 15; the half-space
`B := {z : δᵀ(z − x) ≥ σ‖δ‖Φ⁻¹(1 − p̄B)}` is defined in the proof of Theorem 1, p. 14 (PDF pages).
(The Claim's proof on p. 15 misprints `B` with `≤` and its first line as `ℙ(X ∈ A)`; the
definition of p. 14 is used.)

**Formalization Note.** `X ∼ 𝒩(x, σ²I)` is `gaussNoise x σ`, `Y ∼ 𝒩(x + δ, σ²I)` is
`gaussNoise (x + δ) σ`, `δᵀv` is `inner ℝ δ v`, `Φ⁻¹` is the real inverse `PhiInvReal` on `(0, 1)`.
The hypotheses `δ ≠ 0` and `0 < p < 1` are added: they are implicit in the paper's computation
(it divides by `‖δ‖` and uses `Φ(Φ⁻¹(p)) = p`); at `δ = 0` the half-space is all of `ℝᵈ` or empty
and the identity fails, and in Theorem 1 the case `δ = 0` and the endpoint probabilities are
handled separately. -/
theorem prob_X_B {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d)) (hδ : δ ≠ 0)
    (pB : ℝ) (hpB0 : 0 < pB) (hpB1 : pB < 1) :
    (gaussNoise x σ {z | σ * ‖δ‖ * PhiInvReal (1 - pB) ≤ inner ℝ δ (z - x)}).toReal = pB := by sorry

end Cohen2019.Robust
