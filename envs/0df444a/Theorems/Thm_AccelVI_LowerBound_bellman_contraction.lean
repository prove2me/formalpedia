-- Prove2me | Theorems.Thm_AccelVI_LowerBound_bellman_contraction
-- name    : AccelVI.LowerBound.bellman_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:58.029128+00:00
-- url     : https://prove2.me/theorems/b48acf01-0cfb-4648-accc-d36f57118635
-- title:
--   §2, p. 3 — the Bellman operator T is a λ-contraction of (ℝⁿ, ‖·‖∞)
-- statement:
--   Let $(S, A, P, r, \lambda)$ be a finite MDP with a nonempty action set, in which each $P_{ia}$ is a probability distribution over next states and $\lambda \in (0,1)$, and let $T$ be its Bellman operator (2.1). Then for all $v, w \in \mathbb{R}^n$,
--   $$
--   \|T(v) - T(w)\|_\infty \le \lambda \, \|v - w\|_\infty .
--   $$
--
--   This is the basic contraction property on which value iteration and all the inequalities of §3 rest.
--
--   **Formalization Note.** $\|\cdot\|_\infty$ is Mathlib's sup norm on `S → ℝ`. The state set may be any finite type; for an empty state set both sides are $0$.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 3, §2, sentence after (2.1)

import Mathlib
import Definitions.Def_AccelVI_LowerBound_Setting

namespace AccelVI.LowerBound
theorem bellman_contraction {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    ‖bellman M v - bellman M w‖ ≤ M.lam * ‖v - w‖ := by sorry
end AccelVI.LowerBound
