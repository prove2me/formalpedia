-- Prove2me | Theorems.Thm_AccelVI_LowerBound_eq_3_5
-- name    : AccelVI.LowerBound.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:30.037329+00:00
-- url     : https://prove2.me/theorems/4de79292-d296-4f1f-902a-ebbce7640929
-- title:
--   (3.5), p. 6 — (1 − λ)‖v − w‖∞ ≤ ‖(I − T)(v) − (I − T)(w)‖∞
-- statement:
--   Let $(S, A, P, r, \lambda)$ be a finite MDP with a nonempty action set, in which each $P_{ia}$ is a probability distribution and $\lambda \in (0,1)$, and let $T$ be its Bellman operator (2.1). Writing $(I - T)(v) = v - T(v)$, for all $v, w \in \mathbb{R}^n$,
--   $$
--   (1 - \lambda) \, \|v - w\|_\infty \le \|(I - T)(v) - (I - T)(w)\|_\infty .
--   $$
--
--   This is the analogue for the residual map $I - T$ of strong monotonicity of a gradient, with constant $\mu = 1 - \lambda$. In the lower-bound proof it turns a lower bound on $\|v_s - v^*\|_\infty$ into one on the residual.
--
--   **Formalization Note.** $\|\cdot\|_\infty$ is Mathlib's sup norm on `S → ℝ`.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 6, display (3.5)

import Mathlib
import Definitions.Def_AccelVI_LowerBound_Setting

namespace AccelVI.LowerBound
theorem eq_3_5 {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    (1 - M.lam) * ‖v - w‖ ≤ ‖(v - bellman M v) - (w - bellman M w)‖ := by sorry
end AccelVI.LowerBound
