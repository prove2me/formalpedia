-- Prove2me | Theorems.Thm_ExactPenGNEP_NonShared_eq_5_gradient
-- name    : ExactPenGNEP.NonShared.eq_5_gradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:31.147357+00:00
-- url     : https://prove2.me/theorems/f059de70-854e-4c6a-a69d-279766798b84
-- title:
--   Equation (5), p. 5 — gradient of the ℓq residual outside the set, q ∈ (1, ∞)
-- statement:
--   Let $S = \{x \in \mathbb R^k \mid g_i(x) \le 0,\ i \in [m];\ h_j(x) = 0,\ j \in [p]\}$ be finitely representable with differentiable defining functions $g_i, h_j : \mathbb R^k \to \mathbb R$, and let $q \in (1, \infty)$. The $\ell_q$ residual of $S$ is
--
--   $$r_q(x) = \Big( \sum_{i\in[m]} \max(g_i(x), 0)^q + \sum_{j\in[p]} |h_j(x)|^q \Big)^{1/q}.$$
--
--   At every point $x \notin S$, $r_q$ is differentiable and
--
--   $$\nabla r_q(x) = \frac{1}{r_q^{q-1}(x)} \Big[ \sum_{i\in[m]} (g_i^+(x))^{q-1} \nabla g_i(x) + \sum_{j\in[p]} |h_j(x)|^{q-1} (\operatorname{sgn} h_j(x)) \nabla h_j(x) \Big],$$
--
--   where $g_i^+ = \max(g_i, 0)$ and $\operatorname{sgn}$ is $1$ on positive numbers, $-1$ on negative numbers and $0$ at $0$.
--
--   The formula is used to compute the directional derivative of a player's penalty term at an infeasible penalized equilibrium.
--
--   **Formalization Note** The statement is on $\mathbb R^k$ = `EuclideanSpace ℝ (Fin k)` and gives the Fréchet derivative (`HasFDerivAt`); the gradient is its Riesz representative. The "Moreover" sentence of p. 5 assumes only that the defining functions are differentiable, so convexity of $g_i$ and affinity of $h$ are not assumed; the formula holds without them.
-- source:
--   Ba & Pang, Exact penalization of generalized Nash equilibrium problems, arXiv:1811.10674v2, p. 5, Equations (4)–(5)

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open LeiBR.Sync

namespace ExactPenGNEP.NonShared

theorem eq_5_gradient {k m p : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin k) → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin k) → ℝ) (q : ℝ) (x : EuclideanSpace ℝ (Fin k))
    (hg : ∀ i, Differentiable ℝ (g i)) (hh : ∀ j, Differentiable ℝ (h j)) (hq : 1 < q)
    (hx : x ∉ {y | (∀ i, g i y ≤ 0) ∧ ∀ j, h j y = 0}) :
    HasFDerivAt (lqRes g h q)
      ((1 / lqRes g h q x ^ (q - 1)) •
        (∑ i, (max (g i x) 0) ^ (q - 1) • fderiv ℝ (g i) x +
          ∑ j, (|h j x| ^ (q - 1) * Real.sign (h j x)) • fderiv ℝ (h j) x)) x := by sorry

end ExactPenGNEP.NonShared
