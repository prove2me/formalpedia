-- Prove2me | Theorems.Thm_FastCLO_LowerBound_eq_14
-- name    : FastCLO.LowerBound.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:23.109433+00:00
-- url     : https://prove2.me/theorems/74f9f019-d5dd-4f3b-84fa-1c771e17215a
-- title:
--   Eq. (14), one bit — the error probability of any estimate of a binary parameter is at least the minimum Bayes risk
-- statement:
--   Let a binary parameter $b \in \{0,1\}$ and an observation $\mathcal D$ taking finitely many values $\omega$ have joint probabilities $w_0(\omega) = \tilde{\mathbb P}(b = 0, \mathcal D = \omega)$ and $w_1(\omega) = \tilde{\mathbb P}(b = 1, \mathcal D = \omega)$, and let $\hat b(\omega) \in \{0,1\}$ be any estimate of $b$. Then
--   $$\sum_\omega \min\{w_0(\omega), w_1(\omega)\} \;\le\; \sum_{\omega:\ \hat b(\omega) = 1} w_0(\omega) + \sum_{\omega:\ \hat b(\omega) = 0} w_1(\omega).$$
--   The left side is $\mathbb E_{\tilde{\mathbb P}}\big[\min\{\tilde{\mathbb P}(b=1\mid\mathcal D), 1-\tilde{\mathbb P}(b=1\mid\mathcal D)\}\big]$, the minimum Bayes risk; the right side is $\tilde{\mathbb P}(\hat b \ne b)$.
--
--   This is Eq. (14) of the paper for a single coordinate $b_i$; summing over coordinates and multiplying by $\zeta\rho(\mathcal Z)/\eta$ gives the display. It is the step that turns the regret of an arbitrary algorithm into a quantity that depends only on the data distribution.
--
--   **Formalization Note** The expectations are written as finite sums over the observation space, which covers the finitely supported data of the paper's construction.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 3 (A.2), Eq. (14), p. 21; reused in the proof of Theorem 7, p. 30

import Mathlib

namespace FastCLO.LowerBound

/-- Eq. (14) for one bit (Hu, Kallus, Mao, arXiv:2011.03030v3, proof of Theorem 3, p. 21; reused in
the proof of Theorem 7, p. 30): the probability that an estimate `b̂(D)` of a binary parameter `b`
is wrong is at least the minimum Bayes risk `E[min{P(b = 1 | D), 1 − P(b = 1 | D)}]`.

Formalization Note: the data take finitely many values `ω`; `w0 ω = P(b = 0, D = ω)` and
`w1 ω = P(b = 1, D = ω)`. Then `E[min posterior] = Σ_ω min(w0 ω, w1 ω)` and
`P(b̂ ≠ b) = Σ_ω (w0 ω if b̂(ω) = 1 else w1 ω)`. -/
theorem eq_14 {Ω : Type*} [Fintype Ω] (w0 w1 : Ω → ℝ) (h0 : ∀ ω, 0 ≤ w0 ω) (h1 : ∀ ω, 0 ≤ w1 ω)
    (bhat : Ω → Bool) :
    ∑ ω, min (w0 ω) (w1 ω) ≤ ∑ ω, (if bhat ω then w0 ω else w1 ω) := by sorry

end FastCLO.LowerBound
