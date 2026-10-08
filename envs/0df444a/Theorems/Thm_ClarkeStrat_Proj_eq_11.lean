-- Prove2me | Theorems.Thm_ClarkeStrat_Proj_eq_11
-- name    : ClarkeStrat.Proj.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:22.123124+00:00
-- url     : https://prove2.me/theorems/a575b61f-d096-4cbd-b2cd-f4eaab65b86a
-- title:
--   (11), proof of Proposition 4, p. 562 — Proj_{T_x X_x} ∂̂f(x) ⊂ {∇_R f(x)}
-- statement:
--   This is display (11) in the proof of the projection formula: Fréchet subgradients project onto the stratum gradient.
--
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ and let $\mathcal S=(S_i)_{i\in I}$ be a nonvertical Whitney stratification of $\operatorname{Graph} f$. Let $x\in\operatorname{dom} f$, let $S_x$ be the stratum containing $(x,f(x))$, $T_xX_x=\Pi(T_{(x,f(x))}S_x)$, and let $\nabla_R f(x)$ be the stratum gradient. Then every Fréchet subgradient $x^*\in\hat\partial f(x)$ satisfies
--
--   $$\operatorname{Proj}_{T_xX_x}x^*=\nabla_R f(x),\qquad\text{i.e.}\qquad \operatorname{Proj}_{T_xX_x}\hat\partial f(x)\subset\{\nabla_R f(x)\}.$$
--
--   This is the first step of the proof of Proposition 4: the remaining parts pass to limits of Fréchet subgradients.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $f$ takes values in `EReal` and is never $-\infty$, and the value $f(x)$ is read as a real number only under the hypothesis $f(x)\neq+\infty$. The stratification is taken of class $C^1$ (the weakest case of the paper's hypothesis). The stratum gradient is the vector $g$ given in the hypotheses together with the predicate `IsStratumGrad` ($g\in T_xX_x$ and $(g,-1)\perp T_{(x,f(x))}S_x$); a separate item of the mission shows that this vector exists and is unique. Lower semicontinuity of $f$ is not needed for this step and is omitted, which makes the statement more general.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), https://doi.org/10.1137/060670080, p. 562, (11) in the proof of Proposition 4

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ClarkeStrat_Proj_Setting
open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared ProjLikeRetr.Retractor

namespace ClarkeStrat.Proj

/-- (11), proof of Proposition 4, p. 562: `Proj_{T_x X_x} ∂̂f(x) ⊂ {∇_R f(x)}`. -/
theorem eq_11 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    {I : Type*} (S : I → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hS : IsCpStratification 1 (graphSet f) S ∧ WhitneyA S) (hH : IsNonvertical S)
    (x : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤) (i : I) (hxi : lift x (f x).toReal ∈ S i)
    (g : EuclideanSpace ℝ (Fin n)) (hg : IsStratumGrad (S i) (lift x (f x).toReal) g) :
    ∀ v, IsRegularSubgrad f x v → (tangentX (S i) (lift x (f x).toReal)).starProjection v = g := by sorry

end ClarkeStrat.Proj
