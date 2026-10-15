-- Prove2me | Theorems.Thm_AccelVI_SafeAVI_bellman_contraction
-- name    : AccelVI.SafeAVI.bellman_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:10.201559+00:00
-- url     : https://prove2.me/theorems/97b034dd-0867-4dc4-a515-5fab02a0a14a
-- title:
--   §2, p. 3 — the Bellman operator T is a λ-contraction of (ℝⁿ, ‖·‖∞)
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a finite MDP with a nonempty action set, in which every $P_{ia}$ is a probability distribution over next states and $\lambda\in(0,1)$, and let $T$ be its Bellman operator $T(v)_i = \max_{a}\{r_{ia} + \lambda P_{ia}^\top v\}$. Then for all $v,w\in\mathbb R^{\mathbb S}$,
--
--   $$\|T(v) - T(w)\|_\infty \le \lambda\,\|v - w\|_\infty .$$
--
--   This is the basic fact behind value iteration and behind every convergence argument for the safe accelerated scheme: it bounds the residual after a value-iteration step and ties the residual to the distance to the fixed point.
--
--   **Formalization Note** $\|\cdot\|_\infty$ is Mathlib's sup norm on `S → ℝ`.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 3, §2, sentence after (2.1)

import Mathlib
import Definitions.Def_AccelVI_SafeAVI_Setting

namespace AccelVI.SafeAVI
theorem bellman_contraction {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    ‖bellman M v - bellman M w‖ ≤ M.lam * ‖v - w‖ := by sorry
end AccelVI.SafeAVI
