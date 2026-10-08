-- Prove2me | Theorems.Thm_FosterQueues_GIM1_theorem7_branching_root
-- name    : FosterQueues.GIM1.theorem7_branching_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:39:23.111304+00:00
-- url     : https://prove2.me/theorems/3a48918a-cfa7-4ee8-ad1e-a7339b00cc24
-- title:
--   Theorem 7 — Σ zⁿpₙ = z has a root in (0, 1) iff Σ n pₙ > 1
-- statement:
--   Let $(q_n)_{n \ge 0}$ be a probability distribution on $\{0, 1, 2, \dots\}$, that is $q_n \ge 0$ and $\sum_n q_n = 1$, and assume $q_0 > 0$. Then the equation
--   $$
--   \sum_{n=0}^{\infty} z^n q_n = z
--   $$
--   has a root $\xi$ with $0 < \xi < 1$ if and only if
--   $$
--   \sum_{n=1}^{\infty} n\, q_n > 1,
--   $$
--   where the mean $\sum n q_n$ is allowed to be $+\infty$ (and then the condition holds).
--
--   This is the familiar lemma from the theory of branching processes on the fixed points of a probability generating function. In Foster's paper it supplies, for the GI/M/1 chain with $\rho < 1$, the root $\xi$ of $\sum z^n a_n = z$ from which the summable invariant vector $x_i = \xi^i$ is built.
--
--   **Formalization Note** The paper names the distribution $\{p_n\}$; it is renamed $q$ here so that it is not confused with the transition probabilities $p_{ij}$. The mean is taken in $[0, \infty]$. The equation is stated with `HasSum`, i.e. the series converges to $\xi$; for $0 < \xi < 1$ it always converges.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), Theorem 7, p. 358

import Mathlib

open scoped ENNReal

namespace FosterQueues.GIM1

theorem theorem7_branching_root (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n) (hsum : HasSum q 1)
    (hq0 : 0 < q 0) :
    (∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ HasSum (fun n => ξ ^ n * q n) ξ) ↔
      1 < ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (q n) := by sorry

end FosterQueues.GIM1
