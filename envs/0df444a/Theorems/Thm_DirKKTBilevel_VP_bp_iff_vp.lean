-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_bp_iff_vp
-- name    : DirKKTBilevel.VP.bp_iff_vp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:37.108727+00:00
-- url     : https://prove2.me/theorems/fe9fb321-b392-4179-a95d-b06271d2589b
-- title:
--   §1, p. 2 — (BP) and its value-function reformulation (VP) have the same feasible points
-- statement:
--   Let $f:\mathbb R^n\times\mathbb R^m\to\mathbb R$, $g:\mathbb R^n\times\mathbb R^m\to\mathbb R^p$, $G:\mathbb R^n\times\mathbb R^m\to\mathbb R^q$, let $S(x)$ be the solution set of the lower level program $\min_y f(x,y)$ s.t. $g(x,y)\le0$, and let $V(x)=\inf_y\{f(x,y)\mid g(x,y)\le0\}$ be its value function, with values in $[-\infty,+\infty]$. For every $(x,y)$,
--   $$y\in S(x)\ \text{and}\ G(x,y)\le0\quad\Longleftrightarrow\quad f(x,y)-V(x)\le0,\ \ g(x,y)\le0,\ \ G(x,y)\le0.$$
--
--   Thus (BP) and (VP) have the same feasible set, so they have the same (local) minimizers. This is what allows the theory of the single-level problem (P) to be applied to (BP).
--
--   **Formalization Note** The difference $f(x,y)-V(x)$ is computed in `EReal`; when $V(x)=-\infty$ it equals $+\infty$, so the right-hand side fails, as does the left.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 2, §1, (VP)

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

namespace DirKKTBilevel.VP

/-- §1, p. 2: (BP) and (VP) have the same feasible points. `y ∈ S(x)` and `G(x, y) ≤ 0` hold iff
`f(x, y) − V(x) ≤ 0`, `g(x, y) ≤ 0` and `G(x, y) ≤ 0` (the first inequality in `EReal`). -/
theorem bp_iff_vp {n m p q : ℕ} (f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q)
    (x : E n) (y : E m) :
    (y ∈ solMap f g x ∧ ∀ j, G (WithLp.toLp 2 (x, y)) j ≤ 0) ↔
      ((f (WithLp.toLp 2 (x, y)) : EReal) - valueFn f g x ≤ 0 ∧
        (∀ i, g (WithLp.toLp 2 (x, y)) i ≤ 0) ∧ ∀ j, G (WithLp.toLp 2 (x, y)) j ≤ 0) := by sorry

end DirKKTBilevel.VP
