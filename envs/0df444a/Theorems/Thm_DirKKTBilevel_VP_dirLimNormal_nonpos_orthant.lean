-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_dirLimNormal_nonpos_orthant
-- name    : DirKKTBilevel.VP.dirLimNormal_nonpos_orthant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:32.662394+00:00
-- url     : https://prove2.me/theorems/d4382705-e87e-40a7-8b28-3f8a30d81edd
-- title:
--   Proof of Theorem 3.1, p. 11 (with eq. (1), p. 5) — directional normal cone of the nonpositive orthant
-- statement:
--   Let $a\in\mathbb R^q_-$ (that is, $a\le0$) and let $d\in\mathbb R^q$ be a tangent direction to $\mathbb R^q_-$ at $a$, i.e. $d_j\le0$ whenever $a_j=0$. Then the directional limiting normal cone of $\mathbb R^q_-$ at $a$ in direction $d$ is
--   $$N_{\mathbb R^q_-}(a;d)=\{\xi\in\mathbb R^q\mid 0\le\xi\perp a,\ \xi\perp d\}.$$
--
--   This is equation (1) of the paper for the convex set $\mathbb R^q_-$. In the proof of Theorem 3.1 it is applied with $a=\phi(\bar z)$, $d=\phi'(\bar z;u)$, and it produces the sign and complementarity conditions of the multiplier.
--
--   **Formalization Note** The cone is the published `SetConstrSOC.Directional.dirLimNormal`. The orthogonality relations are inner products: $\sum_j\xi_ja_j=0$ and $\sum_j\xi_jd_j=0$.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 11, proof of Theorem 3.1; p. 5, eq. (1)

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

namespace DirKKTBilevel.VP

/-- Proof of Theorem 3.1, p. 11, with eq. (1), p. 5: for `a ∈ ℝ^q_−` and a tangent direction `d`
(`d_j ≤ 0` whenever `a_j = 0`), the directional limiting normal cone of `ℝ^q_−` at `a` in direction
`d` is `{ξ | 0 ≤ ξ ⊥ a, ξ ⊥ d}`. -/
theorem dirLimNormal_nonpos_orthant {q : ℕ} (a d : E q) (ha : ∀ j, a j ≤ 0)
    (hd : ∀ j, a j = 0 → d j ≤ 0) :
    dirLimNormal {w : E q | ∀ j, w j ≤ 0} a d =
      {ξ | (∀ j, 0 ≤ ξ j) ∧ ∑ j, ξ j * a j = 0 ∧ ∑ j, ξ j * d j = 0} := by sorry

end DirKKTBilevel.VP
