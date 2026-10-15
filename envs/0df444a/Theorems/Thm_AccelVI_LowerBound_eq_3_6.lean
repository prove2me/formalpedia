-- Prove2me | Theorems.Thm_AccelVI_LowerBound_eq_3_6
-- name    : AccelVI.LowerBound.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:19.421866+00:00
-- url     : https://prove2.me/theorems/d9aeb969-1ddc-42c1-852a-41d2e7365be0
-- title:
--   (3.6), p. 6 — ‖(I − T)(v) − (I − T)(w)‖∞ ≤ (1 + λ)‖v − w‖∞
-- statement:
--   Let $(S, A, P, r, \lambda)$ be a finite MDP with a nonempty action set, in which each $P_{ia}$ is a probability distribution and $\lambda \in (0,1)$, and let $T$ be its Bellman operator (2.1). Writing $(I - T)(v) = v - T(v)$, for all $v, w \in \mathbb{R}^n$,
--   $$
--   \|(I - T)(v) - (I - T)(w)\|_\infty \le (1 + \lambda) \, \|v - w\|_\infty .
--   $$
--
--   This is the analogue of the Lipschitz continuity of a gradient, with constant $L = 1 + \lambda$. Taking $w = v^*$ gives $\|v - v^*\|_\infty \ge \|v - T(v)\|_\infty / (1 + \lambda)$, the last step of the proof of Theorem 6.3.
--
--   **Formalization Note.** $\|\cdot\|_\infty$ is Mathlib's sup norm on `S → ℝ`.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 6, display (3.6)

import Mathlib
import Definitions.Def_AccelVI_LowerBound_Setting

namespace AccelVI.LowerBound
theorem eq_3_6 {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    ‖(v - bellman M v) - (w - bellman M w)‖ ≤ (1 + M.lam) * ‖v - w‖ := by sorry
end AccelVI.LowerBound
