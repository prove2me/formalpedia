-- Prove2me | Theorems.Thm_ConvexOptAlg_ProjectedGD_eq_3_7
-- name    : ConvexOptAlg.ProjectedGD.eq_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:12:34.055338+00:00
-- url     : https://prove2.me/theorems/a8a8021b-bbd2-4255-9420-fba69550ad9b
-- title:
--   (3.7), proof of Lemma 3.6, p. 270 — ∇f(x)ᵀ(x⁺ − y) ≤ g_X(x)ᵀ(x⁺ − y)
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be compact and convex, $\beta>0$, $x,y\in\mathcal X$, and let $\nabla f(x)\in\mathbb R^n$ be a vector (the gradient of $f$ at $x$). Let $x^+=\Pi_{\mathcal X}\bigl(x-\tfrac1\beta\nabla f(x)\bigr)$ be the projected gradient step and $g_{\mathcal X}(x)=\beta(x-x^+)$ the gradient mapping. Then
--   $$\nabla f(x)^\top(x^+-y)\le g_{\mathcal X}(x)^\top(x^+-y). \tag{3.7}$$
--
--   This is the first step of the proof of Lemma 3.6: in the constrained case the gradient mapping takes over the role the gradient plays in the unconstrained analysis. It is equivalent to $\bigl(x^+-(x-\tfrac1\beta\nabla f(x))\bigr)^\top(x^+-y)\le0$.
--
--   **Formalization Note** Only the vector $\nabla f(x)$ enters, so the statement is for an arbitrary map `g` standing for $\nabla f$; no property of $f$ is needed. The projection is any point `xplus` with `IsMetricProjection X (x - β⁻¹ • g x) xplus`. $\beta>0$ is the positivity of the smoothness constant implicit in the step $1/\beta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, proof of Lemma 3.6, Eq. (3.7), p. 270

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_ProjectedGD_Defs

open scoped InnerProductSpace
open OnlineConvexOpt.FirstOrder

namespace ConvexOptAlg.ProjectedGD

/-- Display (3.7) in the proof of Lemma 3.6 (Bubeck, arXiv:1405.4980v2, p. 270): for `X` compact
and convex, `β > 0`, `x, y ∈ X` and `x⁺ = Π_X(x − (1/β)∇f(x))` (here `g x` stands for `∇f(x)`),
`∇f(x)ᵀ(x⁺ − y) ≤ g_X(x)ᵀ(x⁺ − y)` with `g_X(x) = β(x − x⁺)`. -/
theorem eq_3_7 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (x y xplus : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hy : y ∈ X)
    (hplus : IsMetricProjection X (x - β⁻¹ • g x) xplus) :
    ⟪g x, xplus - y⟫_ℝ ≤ ⟪gradMap β x xplus, xplus - y⟫_ℝ := by sorry

end ConvexOptAlg.ProjectedGD
