-- Prove2me | Theorems.Thm_ChinesePostman_Polyhedron_w_nonneg_automatic
-- name    : ChinesePostman.Polyhedron.w_nonneg_automatic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:24.599549+00:00
-- url     : https://prove2.me/theorems/16412407-63d5-4c67-8998-2cfaa6d6bd41
-- title:
--   §3, pp. 93–94 — in (3.3) the condition w_n ≥ 0 is automatic for integer w
-- statement:
--   Let $G$ be a finite graph (parallel edges allowed, no loops) and $b_n\in\{0,1\}$ the parity of the degree of node $n$. Let $x\in\mathbb Z^E$ and $w\in\mathbb Z^N$ satisfy $x_e\ge 0$ for every edge and
--   $$\sum_{e\in E}a_{ne}x_e-2w_n=b_n\qquad (n\in N). \tag{3.3}$$
--   Then $w_n\ge 0$ for every node $n$.
--
--   Hence the restrictions $w_n\ge 0$ can be dropped, and the variables $w_n$ eliminated, which is the step from the polyhedron in $(x,w)$ of p. 91 to the polyhedron in $x$ alone.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 93–94, §3, after (3.6)

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem w_nonneg_automatic {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (x : E → ℤ) (w : V → ℤ)
    (hx : ∀ e, 0 ≤ x e) (h33 : ∀ n, incidentSum G x n - 2 * w n = bParity G n) :
    ∀ n, 0 ≤ w n := by sorry

end ChinesePostman.Polyhedron
