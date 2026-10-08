-- Prove2me | Theorems.Thm_ConvexOptAlg_ProjectedGD_lemma_3_6
-- name    : ConvexOptAlg.ProjectedGD.lemma_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:12:58.445535+00:00
-- url     : https://prove2.me/theorems/48fd3ea1-dd53-44b9-a0c7-129c5bf19f84
-- title:
--   Lemma 3.6, p. 270 — f(x⁺) − f(y) ≤ g_X(x)ᵀ(x − y) − (1/(2β))‖g_X(x)‖²
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be compact and convex, and let $f:\mathbb R^n\to\mathbb R$ be convex on $\mathcal X$ and $\beta$-smooth on $\mathcal X$ with $\beta>0$. Let $x,y\in\mathcal X$, let
--   $$x^+=\Pi_{\mathcal X}\Bigl(x-\tfrac1\beta\nabla f(x)\Bigr)\qquad\text{and}\qquad g_{\mathcal X}(x)=\beta(x-x^+).$$
--   Then
--   $$f(x^+)-f(y)\le g_{\mathcal X}(x)^\top(x-y)-\frac1{2\beta}\|g_{\mathcal X}(x)\|^2 .$$
--
--   The lemma makes the gradient mapping the quantity that measures progress in the constrained case: a step decreases $f$ by at least $\frac1{2\beta}\|g_{\mathcal X}(x)\|^2$, and the gap to any feasible $y$ is controlled by $g_{\mathcal X}(x)$. It drives the proofs of Theorem 3.7 and, in a strongly convex form, Theorem 3.10.
--
--   **Formalization Note** $\beta$-smoothness on $\mathcal X$ is the predicate `IsBetaSmoothOn X f g β` (gradient everywhere, nonnegative $\beta$, $\beta$-Lipschitz gradient on $\mathcal X$); convexity is `ConvexOn ℝ X f`. Compactness and convexity of $\mathcal X$ are the standing assumption of Chapter 3; $\beta>0$ is implicit in the step $1/\beta$. The projection is any `xplus` with `IsMetricProjection X (x - β⁻¹ • g x) xplus`.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 3.6, p. 270

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_ProjectedGD_Defs

open scoped InnerProductSpace
open OnlineConvexOpt.FirstOrder

namespace ConvexOptAlg.ProjectedGD

/-- Lemma 3.6 (Bubeck, arXiv:1405.4980v2, p. 270): let `X` be compact and convex, `f` convex and
`β`-smooth on `X` with gradient map `g`, `β > 0`, `x, y ∈ X`, `x⁺ = Π_X(x − (1/β)∇f(x))` and
`g_X(x) = β(x − x⁺)`. Then `f(x⁺) − f(y) ≤ g_X(x)ᵀ(x − y) − (1/(2β))‖g_X(x)‖²`. -/
theorem lemma_3_6 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothOn X f g β)
    (x y xplus : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hy : y ∈ X)
    (hplus : IsMetricProjection X (x - β⁻¹ • g x) xplus) :
    f xplus - f y ≤ ⟪gradMap β x xplus, x - y⟫_ℝ - 1 / (2 * β) * ‖gradMap β x xplus‖ ^ 2 := by sorry

end ConvexOptAlg.ProjectedGD
