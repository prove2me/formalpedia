-- Prove2me | Theorems.Thm_DynSampleSize_Det_eq_4_14
-- name    : DynSampleSize.Det.eq_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:34.461457+00:00
-- url     : https://prove2.me/theorems/c72818e0-654e-4434-9631-bffa3eb856a7
-- title:
--   (4.14) — under (4.8), $\nabla J^T g \ge (1-\theta)\|g\|^2$: $-g$ is a descent direction
-- statement:
--   Let $\theta \in (0,1)$ and let $g, v \in \mathbb{R}^m$ satisfy the relative-error condition (4.8), $\|g - v\| \le \theta\|g\|$. Then
--
--   $$
--   v^T g \;\ge\; (1-\theta)\,\|g\|^2 .
--   $$
--
--   With $g = g_k$ the approximate gradient and $v = \nabla J(w_k)$, this says that $-g_k$ is a descent direction for $J$ at $w_k$, with a quantified angle condition. It is the key input of the one-step decrease (4.15)–(4.16).
--
--   **Formalization Note** The statement is a fact about two arbitrary vectors of `EuclideanSpace ℝ (Fin m)`; $v^Tg$ is the Euclidean inner product `inner ℝ v g`.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 9, (4.14)

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting

open Filter Topology

namespace DynSampleSize.Det

theorem eq_4_14 {m : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (g v : EuclideanSpace ℝ (Fin m)) (h48 : ‖g - v‖ ≤ θ * ‖g‖) :
    (1 - θ) * ‖g‖ ^ 2 ≤ inner ℝ v g := by sorry

end DynSampleSize.Det
