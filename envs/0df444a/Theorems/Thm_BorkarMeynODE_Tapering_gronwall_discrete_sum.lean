-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_gronwall_discrete_sum
-- name    : BorkarMeynODE.Tapering.gronwall_discrete_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:42:44.590214+00:00
-- url     : https://prove2.me/theorems/46b57d74-7e92-463c-bc66-05dbf0f76482
-- title:
--   Lemma 4.3 (i) — discrete Bellman–Gronwall inequality, summed form
-- statement:
--   Let $\{\alpha(n)\}$ and $\{A(n)\}$ be nonnegative real sequences and $\beta>0$ such that
--   $$
--   A(n+1) \le \beta + \sum_{k=0}^{n} \alpha(k)A(k), \qquad n\ge0 .
--   $$
--   Then for all $n\ge1$,
--   $$
--   A(n+1) \le \exp\Big(\sum_{k=1}^{n}\alpha(k)\Big)\big(\alpha(0)A(0)+\beta\big).
--   $$
--
--   This is the discrete Bellman–Gronwall lemma used in the proof of Lemma 4.6 to control the distance between the interpolated iterates and the ODE solution on one block.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 461, Lemma 4.3 (i)

import Mathlib

namespace BorkarMeynODE.Tapering

/-- **Lemma 4.3 (i)** (Borkar–Meyn 2000, p. 461), a discrete Bellman–Gronwall lemma.
If `α, A` are nonnegative sequences, `β > 0`, and
`A(n+1) ≤ β + ∑_{k=0}^{n} α(k) A(k)` for all `n ≥ 0`, then for all `n ≥ 1`
`A(n+1) ≤ exp(∑_{k=1}^{n} α(k)) (α(0) A(0) + β)`. -/
theorem gronwall_discrete_sum (A α : ℕ → ℝ) (β : ℝ)
    (hA : ∀ n, 0 ≤ A n) (hα : ∀ n, 0 ≤ α n) (hβ : 0 < β)
    (hrec : ∀ n : ℕ, A (n + 1) ≤ β + ∑ k ∈ Finset.range (n + 1), α k * A k) :
    ∀ n : ℕ, 1 ≤ n →
      A (n + 1) ≤ Real.exp (∑ k ∈ Finset.Icc 1 n, α k) * (α 0 * A 0 + β) := by sorry

end BorkarMeynODE.Tapering
