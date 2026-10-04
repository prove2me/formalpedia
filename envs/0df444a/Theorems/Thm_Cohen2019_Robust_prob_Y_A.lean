-- Prove2me | Theorems.Thm_Cohen2019_Robust_prob_Y_A
-- name    : Cohen2019.Robust.prob_Y_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:03:38.332676+00:00
-- url     : https://prove2.me/theorems/c10424d7-ffea-467f-ac5c-c037cc1371b3
-- title:
--   Eq. (13) — $\mathbb P(Y \in A) = \Phi(\Phi^{-1}(\underline{p_A}) - \|\delta\|/\sigma)$
-- statement:
--   Let $\sigma > 0$, $x \in \mathbb R^d$, $\delta \in \mathbb R^d$ with $\delta \neq 0$, $Y \sim \mathcal N(x + \delta, \sigma^2 I)$, and $0 < \underline{p_A} < 1$. With the half-space
--   $$
--   A = \{z \in \mathbb R^d : \delta^\top (z - x) \le \sigma \|\delta\|\, \Phi^{-1}(\underline{p_A})\},
--   $$
--   one has
--   $$
--   \mathbb P(Y \in A) = \Phi\Big(\Phi^{-1}(\underline{p_A}) - \frac{\|\delta\|}{\sigma}\Big). \qquad (13)
--   $$
--
--   This is the probability that the "worst-case" classifier of the proof of Theorem 1 still predicts $c_A$ after the input is shifted by $\delta$.
--
--   **Formalization Note** $\Phi$ is the standard Gaussian CDF and $\Phi^{-1}$ its real inverse on $(0,1)$. The hypotheses $\delta \neq 0$ and $0 < \underline{p_A} < 1$ are implicit in the paper's computation.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, proof of Theorem 1, eq. (13), p. 14; Appendix A.0.1, Claim, p. 16 (PDF pages)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Eq. (13): `ℙ(Y ∈ A) = Φ(Φ⁻¹(p̲A) − ‖δ‖/σ)`.** Cohen, Rosenfeld, Kolter, *Certified Adversarial
Robustness via Randomized Smoothing*, arXiv:1902.02918v2, proof of Theorem 1, eq. (13), p. 14;
proved as a Claim in Appendix A.0.1, p. 16 (PDF pages). Here `Y ∼ 𝒩(x + δ, σ²I)` and
`A := {z : δᵀ(z − x) ≤ σ‖δ‖Φ⁻¹(p̲A)}` (p. 14).

**Formalization Note.** `X ∼ 𝒩(x, σ²I)` is `gaussNoise x σ`, `Y ∼ 𝒩(x + δ, σ²I)` is
`gaussNoise (x + δ) σ`, `δᵀv` is `inner ℝ δ v`, `Φ⁻¹` is the real inverse `PhiInvReal` on `(0, 1)`.
The hypotheses `δ ≠ 0` and `0 < p < 1` are added: they are implicit in the paper's computation
(it divides by `‖δ‖` and uses `Φ(Φ⁻¹(p)) = p`); at `δ = 0` the half-space is all of `ℝᵈ` or empty
and the identity fails, and in Theorem 1 the case `δ = 0` and the endpoint probabilities are
handled separately. -/
theorem prob_Y_A {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d)) (hδ : δ ≠ 0)
    (pA : ℝ) (hpA0 : 0 < pA) (hpA1 : pA < 1) :
    (gaussNoise (x + δ) σ {z | inner ℝ δ (z - x) ≤ σ * ‖δ‖ * PhiInvReal pA}).toReal
      = Phi (PhiInvReal pA - ‖δ‖ / σ) := by sorry

end Cohen2019.Robust
