-- Prove2me | Theorems.Thm_ClarkeStrat_Proj_corollary_5_i
-- name    : ClarkeStrat.Proj.corollary_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:06.121633+00:00
-- url     : https://prove2.me/theorems/f1f17c01-8674-4543-a283-0af4a0c795c5
-- title:
--   Corollary 5 (i), p. 563 — the stratum gradient bounds every Clarke subgradient from below
-- statement:
--   This is Corollary 5 (i), the result announced in the abstract.
--
--   Throughout, $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is lower semicontinuous, $\operatorname{dom} f=\{x: f(x)<+\infty\}$, and $\mathcal S=(S_i)_{i\in I}$ is a nonvertical Whitney stratification of $\operatorname{Graph} f\subset\mathbb R^{n+1}$ (all objects as defined in the mission's definitions item). Fix $x\in\operatorname{dom} f$ and the stratum $S_x$ containing $(x,f(x))$. Write $T_xX_x=\Pi(T_{(x,f(x))}S_x)$ for the tangent space of the projected stratum, $\operatorname{Proj}_{T_xX_x}$ for the orthogonal projection of $\mathbb R^n$ onto it, and $\nabla_R f(x)$ for the gradient of $f$ at $x$ relative to the stratum. Then
--
--   $$\|\nabla_R f(x)\|\le\|x^*\|\qquad\text{for all }x^*\in\partial^\circ f(x).$$
--
--   In words: the norm of the gradient of $f$ relative to the stratum through $(x,f(x))$ bounds from below the norm of every Clarke subgradient of $f$ at $x$. In particular every Clarke critical point is a critical point of $f$ restricted to its stratum, which is the step from Proposition 4 to the nonsmooth Morse–Sard theorem and to the Kurdyka–Łojasiewicz inequality of the paper's §4. For $x$ with $\partial^\circ f(x)=\emptyset$ the statement is empty, which is the page's restriction to $x\in\operatorname{dom}\partial^\circ f$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $f$ takes values in `EReal` and is never $-\infty$, and the value $f(x)$ is read as a real number only under the hypothesis $f(x)\neq+\infty$. The stratification is taken of class $C^1$ (the weakest case of the paper's hypothesis). The stratum gradient is the vector $g$ given in the hypotheses together with the predicate `IsStratumGrad` ($g\in T_xX_x$ and $(g,-1)\perp T_{(x,f(x))}S_x$); a separate item of the mission shows that this vector exists and is unique. The paper's hypothesis is a nonvertical $C^p$-Whitney stratification of $\operatorname{Graph} f$; the statement uses $p=1$, which is the most general case.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), https://doi.org/10.1137/060670080, p. 563, Corollary 5 (i), (14)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ClarkeStrat_Proj_Setting
open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared ProjLikeRetr.Retractor

namespace ClarkeStrat.Proj

/-- Corollary 5 (i), (14), p. 563: `‖∇_R f(x)‖ ≤ ‖x*‖` for every Clarke subgradient
`x* ∈ ∂°f(x)`. -/
theorem corollary_5_i {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hlsc : LowerSemicontinuous f) {I : Type*} (S : I → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hS : IsCpStratification 1 (graphSet f) S ∧ WhitneyA S) (hH : IsNonvertical S)
    (x : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤) (i : I) (hxi : lift x (f x).toReal ∈ S i)
    (g : EuclideanSpace ℝ (Fin n)) (hg : IsStratumGrad (S i) (lift x (f x).toReal) g) :
    ∀ v ∈ ClarkeSubdiff f x, ‖g‖ ≤ ‖v‖ := by sorry

end ClarkeStrat.Proj
