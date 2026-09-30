-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_gronwall_discrete_step
-- name    : BorkarMeynODE.Tapering.gronwall_discrete_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:43:04.653375+00:00
-- url     : https://prove2.me/theorems/dd11f977-deb8-4b1a-85be-361fb97eb362
-- title:
--   Lemma 4.3 (ii) — discrete Bellman–Gronwall inequality, one-step form
-- statement:
--   Let $\{\alpha(n)\}$, $\{A(n)\}$ and $\{\gamma(n)\}$ be nonnegative real sequences such that
--   $$
--   A(n+1) \le \big(1+\alpha(n)\big)A(n) + \gamma(n), \qquad n\ge0 .
--   $$
--   Then for all $n\ge1$,
--   $$
--   A(n+1) \le \exp\Big(\sum_{k=1}^{n}\alpha(k)\Big)\Big(\big(1+\alpha(0)\big)A(0) + \beta(n)\Big), \qquad \beta(n) = \sum_{k=0}^{n}\gamma(k).
--   $$
--
--   This version is applied to conditional second moments in the proof of Lemma 4.5. The factor $1+\alpha(0)$ (rather than $e^{\alpha(0)}$) makes it sharper than the textbook discrete Gronwall bound.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 461, Lemma 4.3 (ii)

import Mathlib

namespace BorkarMeynODE.Tapering

/-- **Lemma 4.3 (ii)** (Borkar–Meyn 2000, p. 461), a discrete Bellman–Gronwall lemma.
If `α, A, γ` are nonnegative sequences with `A(n+1) ≤ (1 + α(n)) A(n) + γ(n)` for all
`n ≥ 0`, then for all `n ≥ 1`
`A(n+1) ≤ exp(∑_{k=1}^{n} α(k)) ((1 + α(0)) A(0) + β(n))`, where `β(n) = ∑_{k=0}^{n} γ(k)`. -/
theorem gronwall_discrete_step (A α γ : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hα : ∀ n, 0 ≤ α n) (hγ : ∀ n, 0 ≤ γ n)
    (hrec : ∀ n : ℕ, A (n + 1) ≤ (1 + α n) * A n + γ n) :
    ∀ n : ℕ, 1 ≤ n →
      A (n + 1) ≤ Real.exp (∑ k ∈ Finset.Icc 1 n, α k) *
        ((1 + α 0) * A 0 + ∑ k ∈ Finset.range (n + 1), γ k) := by sorry

end BorkarMeynODE.Tapering
