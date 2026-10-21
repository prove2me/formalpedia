-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_dir_sum_rule
-- name    : DirKKTBilevel.VP.dir_sum_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:59.029115+00:00
-- url     : https://prove2.me/theorems/22b9414a-b2cf-46d7-9614-76c1791fc6c4
-- title:
--   Proof of Theorem 5.2, p. 25 — ∂(f − V)((x̄,ȳ);(u,v)) = ∇f(x̄,ȳ) + ∂(−V)(x̄;u) × {0}
-- statement:
--   Let $f:\mathbb R^n\times\mathbb R^m\to\mathbb R$ be continuously differentiable, $g:\mathbb R^n\times\mathbb R^m\to\mathbb R^p$, and $V(x)=\inf_y\{f(x,y)\mid g(x,y)\le0\}$ the value function. Suppose $V(\bar x)$ is finite. Then for every $\bar y\in\mathbb R^m$ and every direction $(u,v)$,
--   $$\partial(f-V)\big((\bar x,\bar y);(u,v)\big)=\nabla f(\bar x,\bar y)+\partial(-V)(\bar x;u)\times\{0\},$$
--   where $\partial(\cdot)(\cdot\,;\cdot)$ is the directional limiting subdifferential and $(f-V)(x,y)=f(x,y)-V(x)$.
--
--   The directional subdifferential of the difficult constraint $f-V$ of (VP) thus splits into a gradient and the directional subdifferential of $-V$ in the $x$-variable alone. This is how the multiplier condition of Theorem 3.1, applied to (VP), becomes the condition of Theorem 5.1.
--
--   **Formalization Note** The paper uses this identity inside the proof of Theorem 5.2, where $V$ is assumed directionally Lipschitz; only finiteness of $V(\bar x)$ is assumed here, which is weaker. The difference $f-V$ is computed in `EReal`.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 25, proof of Theorem 5.2 (citing [28, Theorem 5.6])

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

namespace DirKKTBilevel.VP

/-- Proof of Theorem 5.2, p. 25 (citing [28, Theorem 5.6]): for continuously differentiable `f`
and finite `V(x̄)`, `∂(f − V)((x̄, ȳ); (u, v)) = ∇f(x̄, ȳ) + ∂(−V)(x̄; u) × {0}`. -/
theorem dir_sum_rule {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p) (hf : ContDiff ℝ 1 f)
    (x : E n) (y : E m) (u : E n) (v : E m)
    (hVbot : valueFn f g x ≠ ⊥) (hVtop : valueFn f g x ≠ ⊤) :
    dirSubdiff (fun z : Z n m => (f z : EReal) - valueFn f g (WithLp.ofLp z).1)
        (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) =
      {w | ∃ ξ ∈ dirSubdiff (fun x' => -(valueFn f g x')) x u,
        w = gradient f (WithLp.toLp 2 (x, y)) + WithLp.toLp 2 (ξ, 0)} := by sorry

end DirKKTBilevel.VP
