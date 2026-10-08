-- Prove2me | Theorems.Thm_ClarkeStrat_Proj_prop_4_eq_10
-- name    : ClarkeStrat.Proj.prop_4_eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:48.283979+00:00
-- url     : https://prove2.me/theorems/d0ceac04-39c7-46e2-b89c-2ea13fa0687d
-- title:
--   Proposition 4 (10), p. 561 — Proj_{T_x X_x} ∂°f(x) ⊂ {∇_R f(x)}
-- statement:
--   This is the second display (10) of the projection formula, Proposition 4.
--
--   Throughout, $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is lower semicontinuous, $\operatorname{dom} f=\{x: f(x)<+\infty\}$, and $\mathcal S=(S_i)_{i\in I}$ is a nonvertical Whitney stratification of $\operatorname{Graph} f\subset\mathbb R^{n+1}$ (all objects as defined in the mission's definitions item). Fix $x\in\operatorname{dom} f$ and the stratum $S_x$ containing $(x,f(x))$. Write $T_xX_x=\Pi(T_{(x,f(x))}S_x)$ for the tangent space of the projected stratum, $\operatorname{Proj}_{T_xX_x}$ for the orthogonal projection of $\mathbb R^n$ onto it, and $\nabla_R f(x)$ for the gradient of $f$ at $x$ relative to the stratum. Then every Clarke subgradient $x^*\in\partial^\circ f(x)$ satisfies
--
--   $$\operatorname{Proj}_{T_xX_x}x^*=\nabla_R f(x),\qquad\text{i.e.}\qquad\operatorname{Proj}_{T_xX_x}\partial^\circ f(x)\subset\{\nabla_R f(x)\}.$$
--
--   The inclusion may be strict because $\partial^\circ f(x)$ may be empty (Remark 4). It is the statement from which Corollary 5 follows.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $f$ takes values in `EReal` and is never $-\infty$, and the value $f(x)$ is read as a real number only under the hypothesis $f(x)\neq+\infty$. The stratification is taken of class $C^1$ (the weakest case of the paper's hypothesis). The stratum gradient is the vector $g$ given in the hypotheses together with the predicate `IsStratumGrad` ($g\in T_xX_x$ and $(g,-1)\perp T_{(x,f(x))}S_x$); a separate item of the mission shows that this vector exists and is unique.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), https://doi.org/10.1137/060670080, p. 561, Proposition 4 (projection formula), (10)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ClarkeStrat_Proj_Setting
open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared ProjLikeRetr.Retractor

namespace ClarkeStrat.Proj

/-- Proposition 4, (10), p. 561: `Proj_{T_x X_x} ∂°f(x) ⊂ {∇_R f(x)}`. -/
theorem prop_4_eq_10 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hlsc : LowerSemicontinuous f) {I : Type*} (S : I → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hS : IsCpStratification 1 (graphSet f) S ∧ WhitneyA S) (hH : IsNonvertical S)
    (x : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤) (i : I) (hxi : lift x (f x).toReal ∈ S i)
    (g : EuclideanSpace ℝ (Fin n)) (hg : IsStratumGrad (S i) (lift x (f x).toReal) g) :
    ∀ v ∈ ClarkeSubdiff f x, (tangentX (S i) (lift x (f x).toReal)).starProjection v = g := by sorry

end ClarkeStrat.Proj
