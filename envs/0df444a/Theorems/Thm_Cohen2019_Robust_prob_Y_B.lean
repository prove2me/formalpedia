-- Prove2me | Theorems.Thm_Cohen2019_Robust_prob_Y_B
-- name    : Cohen2019.Robust.prob_Y_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:03:48.654251+00:00
-- url     : https://prove2.me/theorems/beb8784c-b0d1-4655-bde7-9daaa80de0a1
-- title:
--   Eq. (14) — $\mathbb P(Y \in B) = \Phi(\Phi^{-1}(\overline{p_B}) + \|\delta\|/\sigma)$
-- statement:
--   Let $\sigma > 0$, $x \in \mathbb R^d$, $\delta \in \mathbb R^d$ with $\delta \neq 0$, $Y \sim \mathcal N(x + \delta, \sigma^2 I)$, and $0 < \overline{p_B} < 1$. With the half-space
--   $$
--   B = \{z \in \mathbb R^d : \delta^\top (z - x) \ge \sigma \|\delta\|\, \Phi^{-1}(1 - \overline{p_B})\},
--   $$
--   one has
--   $$
--   \mathbb P(Y \in B) = \Phi\Big(\Phi^{-1}(\overline{p_B}) + \frac{\|\delta\|}{\sigma}\Big). \qquad (14)
--   $$
--
--   This is the probability that the "worst-case" classifier of the proof of Theorem 1 predicts the runner-up class after the input is shifted by $\delta$.
--
--   **Formalization Note** $\Phi$ is the standard Gaussian CDF and $\Phi^{-1}$ its real inverse on $(0,1)$. The hypotheses $\delta \neq 0$ and $0 < \overline{p_B} < 1$ are implicit in the paper's computation.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, proof of Theorem 1, eq. (14), p. 14; Appendix A.0.1, Claim, p. 16 (PDF pages)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Eq. (14): `ℙ(Y ∈ B) = Φ(Φ⁻¹(p̄B) + ‖δ‖/σ)`.** Cohen, Rosenfeld, Kolter, *Certified Adversarial
Robustness via Randomized Smoothing*, arXiv:1902.02918v2, proof of Theorem 1, eq. (14), p. 14;
proved as a Claim in Appendix A.0.1, p. 16 (PDF pages). Here `Y ∼ 𝒩(x + δ, σ²I)` and
`B := {z : δᵀ(z − x) ≥ σ‖δ‖Φ⁻¹(1 − p̄B)}` (p. 14).

**Formalization Note.** `X ∼ 𝒩(x, σ²I)` is `gaussNoise x σ`, `Y ∼ 𝒩(x + δ, σ²I)` is
`gaussNoise (x + δ) σ`, `δᵀv` is `inner ℝ δ v`, `Φ⁻¹` is the real inverse `PhiInvReal` on `(0, 1)`.
The hypotheses `δ ≠ 0` and `0 < p < 1` are added: they are implicit in the paper's computation
(it divides by `‖δ‖` and uses `Φ(Φ⁻¹(p)) = p`); at `δ = 0` the half-space is all of `ℝᵈ` or empty
and the identity fails, and in Theorem 1 the case `δ = 0` and the endpoint probabilities are
handled separately. -/
theorem prob_Y_B {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d)) (hδ : δ ≠ 0)
    (pB : ℝ) (hpB0 : 0 < pB) (hpB1 : pB < 1) :
    (gaussNoise (x + δ) σ {z | σ * ‖δ‖ * PhiInvReal (1 - pB) ≤ inner ℝ δ (z - x)}).toReal
      = Phi (PhiInvReal pB + ‖δ‖ / σ) := by sorry

end Cohen2019.Robust
