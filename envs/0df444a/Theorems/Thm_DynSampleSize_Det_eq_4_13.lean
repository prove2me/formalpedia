-- Prove2me | Theorems.Thm_DynSampleSize_Det_eq_4_13
-- name    : DynSampleSize.Det.eq_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:42.200195+00:00
-- url     : https://prove2.me/theorems/94032ec0-ab0b-4465-a981-4416bab0b258
-- title:
--   (4.13) — under (4.8), $(1-\theta)\|g\| \le \|\nabla J\| \le (1+\theta)\|g\|$
-- statement:
--   Let $\theta \in (0,1)$ and let $g, v \in \mathbb{R}^m$ satisfy the relative-error condition (4.8),
--
--   $$
--   \|g - v\| \le \theta\,\|g\| .
--   $$
--
--   Then
--
--   $$
--   \|v\| \le (1+\theta)\,\|g\| \qquad\text{and}\qquad \|v\| \ge (1-\theta)\,\|g\| .
--   $$
--
--   In the paper $g = g_k$ is the approximate gradient and $v = \nabla J(w_k)$ the true gradient at the iterate $w_k$: under (4.8) the norms of the true and approximate gradients are comparable within the factors $1 \pm \theta$.
--
--   **Formalization Note** The statement is a fact about two arbitrary vectors of $\mathbb{R}^m$ (`EuclideanSpace ℝ (Fin m)`); $v$ plays the role of $\nabla J(w_k)$.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 9, (4.13)

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting

open Filter Topology

namespace DynSampleSize.Det

theorem eq_4_13 {m : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (g v : EuclideanSpace ℝ (Fin m)) (h48 : ‖g - v‖ ≤ θ * ‖g‖) :
    ‖v‖ ≤ (1 + θ) * ‖g‖ ∧ (1 - θ) * ‖g‖ ≤ ‖v‖ := by sorry

end DynSampleSize.Det
