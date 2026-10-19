-- Prove2me | Theorems.Thm_AccelVI_LowerBound_theorem_6_3
-- name    : AccelVI.LowerBound.theorem_6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:06.801335+00:00
-- url     : https://prove2.me/theorems/5338c081-73c9-4c5e-ad42-33cb8ca97bac
-- title:
--   Theorem 6.3, p. 12 — on the n-state chain MDP every first-order method has ‖v_s − v*‖∞ ≥ λ^s/(1 + λ) for s = 1, …, n − 1
-- statement:
--   Let $n \in \mathbb{N}$ and $\lambda \in (0,1)$, and consider the $n$-state chain MDP of Figure 1: one action, state 1 absorbing with reward $r_1 = 1$, and for $i \ge 2$ a deterministic transition from $i$ to $i - 1$ with reward $0$. Let $T$ be its Bellman operator (2.1) and $v^*$ its fixed point, $T(v^*) = v^*$. Let $(v_s)_{s \ge 0}$ be any sequence of iterates with
--   $$
--   v_0 = 0, \qquad v_{s+1} \in \operatorname{span}\{v_0, \dots, v_s, T(v_0), \dots, T(v_s)\}, \quad s \ge 0 .
--   $$
--   Then for every step $s \in \{1, \dots, n-1\}$,
--   $$
--   \|v_s - v^*\|_\infty \ge \frac{\lambda^s}{1 + \lambda} .
--   $$
--
--   So no first-order method, in the sense of iterates built from linear combinations of past iterates and their Bellman images, can converge faster than at rate $\lambda$ uniformly over MDPs, which is the rate of plain value iteration. Acceleration as in convex optimization, which improves $\lambda$ to roughly $1 - \sqrt{1 - \lambda}$, is therefore impossible for general MDPs.
--
--   **Formalization Note.** The paper states "there exists an MDP instance" with $n$ its number of states; its proof fixes an arbitrary $n$ and an arbitrary $\lambda \in (0,1)$ and uses the chain of Figure 1. The statement here is that proof's claim, for every $n$ and $\lambda$ on the explicit chain; the printed existential follows from it. States are 0-based (`Fin n`), "span" is the real linear span, $v^*$ enters through the fixed-point equation $T(v^*) = v^*$, $\|\cdot\|_\infty$ is the sup norm, and $n - 1$ is natural-number subtraction (so the statement has content for $n \ge 2$).
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 12, Theorem 6.3 and its proof, Figure 1

import Mathlib
import Definitions.Def_AccelVI_LowerBound_Setting

namespace AccelVI.LowerBound
theorem theorem_6_3 (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (vstar : Fin n → ℝ)
    (hfix : bellman (chainMDP n lam) vstar = vstar) (v : ℕ → Fin n → ℝ)
    (hv : IsFirstOrder (bellman (chainMDP n lam)) v) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ n - 1) :
    lam ^ s / (1 + lam) ≤ ‖v s - vstar‖ := by sorry
end AccelVI.LowerBound
