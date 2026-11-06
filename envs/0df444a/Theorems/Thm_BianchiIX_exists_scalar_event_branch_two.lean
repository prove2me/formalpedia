-- Prove2me | Theorems.Thm_BianchiIX_exists_scalar_event_branch_two
-- name    : BianchiIX.exists_scalar_event_branch_two
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:59:09.633424+00:00
-- url     : https://prove2.me/theorems/d96acb83-0df7-420c-b209-8643217874ce
-- title:
--   A transverse scalar equation gives a unique twice differentiable event branch
-- statement:
--   Let $E$ be a real Banach space and $Q:E\times\mathbb R\to\mathbb R$
--   be $C^2$ at $(x,t)$. Suppose $u\mapsto Q(x,u)$ has derivative $a\ne0$
--   at $t$. There is $\tau:E\to\mathbb R$ such that
--   $$\tau(x)=t,\qquad \tau\text{ is }C^2\text{ at }x,\qquad
--   d\tau_x=-a^{-1}\,dQ_{(x,t)}\circ(v\mapsto(v,0)).$$
--   For $y$ near $x$, $Q(y,\tau(y))=Q(x,t)$; for $(y,u)$ near $(x,t)$,
--   $$Q(y,u)=Q(x,t)\quad\Longleftrightarrow\quad\tau(y)=u.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ImplicitEvent.lean#L11-L43

import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology

theorem BianchiIX.exists_scalar_event_branch_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    (hQ : ContDiffAt ℝ 2 Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0) :
    ∃ τ : E → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
      HasFDerivAt τ (-a⁻¹ • (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x ∧
      (∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) ∧
      (∀ᶠ z in 𝓝 (x, t), Q z = Q (x, t) ↔ τ z.1 = z.2) := by sorry
