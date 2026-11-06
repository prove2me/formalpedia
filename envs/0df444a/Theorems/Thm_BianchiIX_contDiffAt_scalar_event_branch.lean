-- Prove2me | Theorems.Thm_BianchiIX_contDiffAt_scalar_event_branch
-- name    : BianchiIX.contDiffAt_scalar_event_branch
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:05:58.400789+00:00
-- url     : https://prove2.me/theorems/eaf28483-b93f-4265-9bee-143699ccf34b
-- title:
--   A continuous transverse branch inherits the regularity of its equation
-- statement:
--   Let $E$ be a real Banach space, $Q:E\times\mathbb R\to\mathbb R$,
--   and $n\in\mathbb N\cup\{\infty,\omega\}$ with $n\ne0$, where
--   $C^\omega$ means analytic. Suppose $Q$ is $C^n$ at $(x,t)$ and
--   $\partial_tQ(x,t)=a\ne0$. Let $\tau:E\to\mathbb R$ be continuous at
--   $x$, with $\tau(x)=t$ and
--   $$Q(y,\tau(y))=Q(x,t)$$
--   for all $y$ sufficiently near $x$. Then $\tau$ is $C^n$ at $x$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ImplicitBranch.lean#L11-L39

import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology

theorem BianchiIX.contDiffAt_scalar_event_branch {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    {n : WithTop ℕ∞} (hn : n ≠ 0) (hQ : ContDiffAt ℝ n Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0)
    {τ : E → ℝ} (hτ : τ x = t) (hcτ : ContinuousAt τ x)
    (hhit : ∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) : ContDiffAt ℝ n τ x := by sorry
