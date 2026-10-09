-- Prove2me | Theorems.Thm_DIGing_Push_relation_48
-- name    : DIGing.Push.relation_48
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:30.1629+00:00
-- url     : https://prove2.me/theorems/29ae1001-a835-449e-a16c-2d8bbbfdc956
-- title:
--   (48), p. 22 — the equivalent recursion x(k+1) = R̃(k)(x(k) − αh(k)), h(k+1) = R̃(k)h(k) + V(k+1)⁻¹(∇f(x(k+1)) − ∇f(x(k)))
-- statement:
--   Let the mixing matrices $C(k)$ satisfy Assumption 7, and let $(\mathbf u,\mathbf x,\mathbf y)$ be a run of Push-DIGing with any step size $\alpha$. Write $\mathbf v(k)$ for the push-sum weights, $V(k)=\operatorname{diag}\{\mathbf v(k)\}$, $\tilde R(k)=V(k+1)^{-1}C(k)V(k)$ and $\mathbf h(k)=V(k)^{-1}\mathbf y(k)$. Then for every $k\ge0$
--   $$\mathbf x(k+1)=\tilde R(k)\big(\mathbf x(k)-\alpha\mathbf h(k)\big),\qquad \mathbf h(k+1)=\tilde R(k)\mathbf h(k)+V(k+1)^{-1}\big(\nabla\mathbf f(\mathbf x(k+1))-\nabla\mathbf f(\mathbf x(k))\big).$$
--
--   This is the form of Push-DIGing on which the whole convergence analysis rests: it has the shape of DIGing with the row stochastic matrices $\tilde R(k)$ in place of the doubly stochastic $W(k)$.
--
--   **Formalization Note** Assumption 7 includes the self-weight $C_{jj}(k)=1/(d^{\rm out}_j(k)+1)$ (disclosed in the Setting file); it is what makes every $v_i(k)$ positive, so that $\mathbf u(k)=V(k)\mathbf x(k)$. Assumption 6 is not needed.
-- source:
--   arXiv:1607.03218v3, §5, display (48), p. 22

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem relation_48 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (A : ℕ → Finset (Fin n × Fin n)) (C : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (h7 : Assumption7 A C) (α : ℝ) (u x y : ℕ → DIGing.Undir.Stack n p)
    (hrun : IsPushDIGingRun f C α u x y) :
    ∀ k, x (k + 1) = DIGing.Undir.mix (Rt C k) (x k - α • hSeq C y k) ∧
      hSeq C y (k + 1) = DIGing.Undir.mix (Rt C k) (hSeq C y k) +
        (fun i => (vSeq C (k + 1) i)⁻¹ • (DIGing.Undir.gradStack f (x (k + 1)) - DIGing.Undir.gradStack f (x k)) i) := by sorry

end DIGing.Push
