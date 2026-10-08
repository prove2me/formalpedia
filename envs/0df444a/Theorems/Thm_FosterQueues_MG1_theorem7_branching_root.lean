-- Prove2me | Theorems.Thm_FosterQueues_MG1_theorem7_branching_root
-- name    : FosterQueues.MG1.theorem7_branching_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:03:59.514532+00:00
-- url     : https://prove2.me/theorems/47449922-dfa4-4935-822e-edf01c0eb6fc
-- title:
--   Theorem 7 — Σ zⁿpₙ = z has a root in (0, 1) iff Σ n pₙ > 1
-- statement:
--   Let $q_0,q_1,q_2,\dots$ be a probability distribution on $\{0,1,2,\dots\}$ (so $q_n\ge0$ and $\sum_n q_n=1$) with $q_0>0$. Then the equation
--   $$
--   \sum_{n=0}^{\infty}z^n q_n = z
--   $$
--   has a root $\xi$ with $0<\xi<1$ if and only if
--   $$
--   \sum_{n=1}^{\infty}n\,q_n>1 .
--   $$
--
--   This is the familiar lemma from branching-process theory: the generating function of the offspring law has a fixed point strictly inside $(0,1)$ exactly when the mean exceeds one. Foster uses it in §3 with $q_n=k_n$ to build, when $\rho>1$, the bounded nonconstant solution $y_j=\xi^j$ of (7) that makes the M/G/1 system transient.
--
--   **Formalization Note** The paper writes the distribution as $\{p_n\}$; it is renamed $q$ here to avoid a clash with the transition probabilities $p_{ij}$. The mean $\sum_{n\ge1}nq_n$ is taken in $[0,\infty]$, so an infinite mean counts as exceeding one. For $0<\xi<1$ the series $\sum_n\xi^nq_n$ converges, so it is an ordinary real sum.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), Theorem 7, p. 358

import Mathlib

open scoped ENNReal

namespace FosterQueues.MG1

/-- Foster (1953), Theorem 7, p. 358: for a probability distribution `q₀, q₁, …` on `ℕ` with
`q₀ > 0`, the equation `∑_n zⁿ qₙ = z` has a root `ξ` with `0 < ξ < 1` if and only if
`∑_{n ≥ 1} n qₙ > 1` (the mean taken in `[0, ∞]`). The paper calls the sequence `pₙ`. -/
theorem theorem7_branching_root (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n) (hsum : HasSum q 1)
    (hq0 : 0 < q 0) :
    (∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ ∑' n : ℕ, ξ ^ n * q n = ξ) ↔
      1 < ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (q n) := by sorry

end FosterQueues.MG1
