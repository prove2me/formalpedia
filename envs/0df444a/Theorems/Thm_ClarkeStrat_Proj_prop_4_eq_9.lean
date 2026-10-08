-- Prove2me | Theorems.Thm_ClarkeStrat_Proj_prop_4_eq_9
-- name    : ClarkeStrat.Proj.prop_4_eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:20.208977+00:00
-- url     : https://prove2.me/theorems/71902089-6a3b-4738-92d6-86769d76ebce
-- title:
--   Proposition 4 (9), p. 561 — Proj ∂f(x) ⊂ {∇_R f(x)} and Proj ∂^∞f(x) = {0}
-- statement:
--   This is the first display (9) of the projection formula, Proposition 4.
--
--   Throughout, $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is lower semicontinuous, $\operatorname{dom} f=\{x: f(x)<+\infty\}$, and $\mathcal S=(S_i)_{i\in I}$ is a nonvertical Whitney stratification of $\operatorname{Graph} f\subset\mathbb R^{n+1}$ (all objects as defined in the mission's definitions item). Fix $x\in\operatorname{dom} f$ and the stratum $S_x$ containing $(x,f(x))$. Write $T_xX_x=\Pi(T_{(x,f(x))}S_x)$ for the tangent space of the projected stratum, $\operatorname{Proj}_{T_xX_x}$ for the orthogonal projection of $\mathbb R^n$ onto it, and $\nabla_R f(x)$ for the gradient of $f$ at $x$ relative to the stratum. Then
--
--   $$\operatorname{Proj}_{T_xX_x}\partial f(x)\subset\{\nabla_R f(x)\},\qquad \operatorname{Proj}_{T_xX_x}\partial^\infty f(x)=\{0\}.$$
--
--   The second relation is an equality of sets: the projection of the singular subdifferential is exactly $\{0\}$, which includes the fact that $\partial^\infty f(x)$ is nonempty.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $f$ takes values in `EReal` and is never $-\infty$, and the value $f(x)$ is read as a real number only under the hypothesis $f(x)\neq+\infty$. The stratification is taken of class $C^1$ (the weakest case of the paper's hypothesis). The stratum gradient is the vector $g$ given in the hypotheses together with the predicate `IsStratumGrad` ($g\in T_xX_x$ and $(g,-1)\perp T_{(x,f(x))}S_x$); a separate item of the mission shows that this vector exists and is unique.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), https://doi.org/10.1137/060670080, p. 561, Proposition 4 (projection formula), (9)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ClarkeStrat_Proj_Setting
open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared ProjLikeRetr.Retractor

namespace ClarkeStrat.Proj

/-- Proposition 4, (9), p. 561: `Proj_{T_x X_x} ∂f(x) ⊂ {∇_R f(x)}` and
`Proj_{T_x X_x} ∂^∞f(x) = {0}`. -/
theorem prop_4_eq_9 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hlsc : LowerSemicontinuous f) {I : Type*} (S : I → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hS : IsCpStratification 1 (graphSet f) S ∧ WhitneyA S) (hH : IsNonvertical S)
    (x : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤) (i : I) (hxi : lift x (f x).toReal ∈ S i)
    (g : EuclideanSpace ℝ (Fin n)) (hg : IsStratumGrad (S i) (lift x (f x).toReal) g) :
    (∀ v ∈ LimitingSubdiff f x, (tangentX (S i) (lift x (f x).toReal)).starProjection v = g) ∧
      (tangentX (S i) (lift x (f x).toReal)).starProjection '' SingularSubdiff f x = {0} := by sorry

end ClarkeStrat.Proj
