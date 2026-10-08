-- Prove2me | Theorems.Thm_ClarkeStrat_Proj_eq_12_singular
-- name    : ClarkeStrat.Proj.eq_12_singular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:39.752297+00:00
-- url     : https://prove2.me/theorems/a972a492-bc94-4f32-a09b-3a2073d26715
-- title:
--   (12), second part, p. 562 — Proj_{T_x X_x} ∂^∞f(x) ⊂ {0}
-- statement:
--   This is the second half of display (12) in the proof of the projection formula: singular limiting subgradients are orthogonal to the projected stratum.
--
--   Throughout, $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is lower semicontinuous, $\operatorname{dom} f=\{x: f(x)<+\infty\}$, and $\mathcal S=(S_i)_{i\in I}$ is a nonvertical Whitney stratification of $\operatorname{Graph} f\subset\mathbb R^{n+1}$ (all objects as defined in the mission's definitions item). Fix $x\in\operatorname{dom} f$ and the stratum $S_x$ containing $(x,f(x))$. Write $T_xX_x=\Pi(T_{(x,f(x))}S_x)$ for the tangent space of the projected stratum, $\operatorname{Proj}_{T_xX_x}$ for the orthogonal projection of $\mathbb R^n$ onto it, and $\nabla_R f(x)$ for the gradient of $f$ at $x$ relative to the stratum. Then every singular subgradient $q\in\partial^\infty f(x)$ satisfies
--
--   $$\operatorname{Proj}_{T_xX_x}q=0,\qquad\text{i.e.}\qquad \partial^\infty f(x)\subset (T_xX_x)^\perp .$$
--
--   Combined with $0\in\partial^\infty f(x)$ (Remark 2 (ii)) this is the equality $\operatorname{Proj}_{T_xX_x}\partial^\infty f(x)=\{0\}$ of (9).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $f$ takes values in `EReal` and is never $-\infty$, and the value $f(x)$ is read as a real number only under the hypothesis $f(x)\neq+\infty$. The stratification is taken of class $C^1$ (the weakest case of the paper's hypothesis). The stratum gradient does not appear in this statement.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), https://doi.org/10.1137/060670080, p. 562, (12) (second part), proof of Proposition 4

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ClarkeStrat_Proj_Setting
open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared ProjLikeRetr.Retractor

namespace ClarkeStrat.Proj

/-- (12), second part, proof of Proposition 4, p. 562: `Proj_{T_x X_x} ∂^∞f(x) ⊂ {0}`. -/
theorem eq_12_singular {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hlsc : LowerSemicontinuous f) {I : Type*} (S : I → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hS : IsCpStratification 1 (graphSet f) S ∧ WhitneyA S) (hH : IsNonvertical S)
    (x : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤) (i : I) (hxi : lift x (f x).toReal ∈ S i) :
    ∀ q ∈ SingularSubdiff f x, (tangentX (S i) (lift x (f x).toReal)).starProjection q = 0 := by sorry

end ClarkeStrat.Proj
