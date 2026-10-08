-- Prove2me | Theorems.Thm_ClarkeStrat_Proj_eq_12_limiting
-- name    : ClarkeStrat.Proj.eq_12_limiting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:20.28451+00:00
-- url     : https://prove2.me/theorems/0830ffdf-8ada-4230-b2d5-0ef2a8e51fae
-- title:
--   (12), first part, p. 562 — Proj_{T_x X_x} ∂f(x) ⊂ {∇_R f(x)}
-- statement:
--   This is the first half of display (12) in the proof of the projection formula: limiting subgradients project onto the stratum gradient.
--
--   Throughout, $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is lower semicontinuous, $\operatorname{dom} f=\{x: f(x)<+\infty\}$, and $\mathcal S=(S_i)_{i\in I}$ is a nonvertical Whitney stratification of $\operatorname{Graph} f\subset\mathbb R^{n+1}$ (all objects as defined in the mission's definitions item). Fix $x\in\operatorname{dom} f$ and the stratum $S_x$ containing $(x,f(x))$. Write $T_xX_x=\Pi(T_{(x,f(x))}S_x)$ for the tangent space of the projected stratum, $\operatorname{Proj}_{T_xX_x}$ for the orthogonal projection of $\mathbb R^n$ onto it, and $\nabla_R f(x)$ for the gradient of $f$ at $x$ relative to the stratum. Then every limiting subgradient $p\in\partial f(x)$ satisfies
--
--   $$\operatorname{Proj}_{T_xX_x}p=\nabla_R f(x),\qquad\text{i.e.}\qquad\operatorname{Proj}_{T_xX_x}\partial f(x)\subset\{\nabla_R f(x)\}.$$
--
--   Together with the second half of (12) this gives the first inclusion of (9) and, after taking closed convex hulls, (10).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $f$ takes values in `EReal` and is never $-\infty$, and the value $f(x)$ is read as a real number only under the hypothesis $f(x)\neq+\infty$. The stratification is taken of class $C^1$ (the weakest case of the paper's hypothesis). The stratum gradient is the vector $g$ given in the hypotheses together with the predicate `IsStratumGrad` ($g\in T_xX_x$ and $(g,-1)\perp T_{(x,f(x))}S_x$); a separate item of the mission shows that this vector exists and is unique.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), https://doi.org/10.1137/060670080, p. 562, (12) (first part) and (13), proof of Proposition 4

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ClarkeStrat_Proj_Setting
open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared ProjLikeRetr.Retractor

namespace ClarkeStrat.Proj

/-- (12), first part, proof of Proposition 4, p. 562: `Proj_{T_x X_x} ∂f(x) ⊂ {∇_R f(x)}`. -/
theorem eq_12_limiting {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hlsc : LowerSemicontinuous f) {I : Type*} (S : I → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hS : IsCpStratification 1 (graphSet f) S ∧ WhitneyA S) (hH : IsNonvertical S)
    (x : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤) (i : I) (hxi : lift x (f x).toReal ∈ S i)
    (g : EuclideanSpace ℝ (Fin n)) (hg : IsStratumGrad (S i) (lift x (f x).toReal) g) :
    ∀ v ∈ LimitingSubdiff f x, (tangentX (S i) (lift x (f x).toReal)).starProjection v = g := by sorry

end ClarkeStrat.Proj
