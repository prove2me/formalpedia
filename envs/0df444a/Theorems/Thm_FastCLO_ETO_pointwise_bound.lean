-- Prove2me | Theorems.Thm_FastCLO_ETO_pointwise_bound
-- name    : FastCLO.ETO.pointwise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:43.773002+00:00
-- url     : https://prove2.me/theorems/c9e26228-0f94-42c6-90bd-dc1cae8e3c32
-- title:
--   Proof of Theorem 8, first display — a decision optimal for the estimate v costs at most 2B‖u − v‖ extra under the true cost u
-- statement:
--   Let $\mathcal Z \subseteq \mathbb R^d$ be a polytope with $\|z\| \le B$ for all $z \in \mathcal Z$. Let $u, v \in \mathbb R^d$, let $z_1 \in \mathcal Z$ minimize $v^\top z$ over $z \in \mathcal Z$, and let $z_2 \in \mathcal Z$ be arbitrary. Then
--
--   $$u^\top (z_1 - z_2) \le 2B\,\|u - v\|.$$
--
--   In the paper $u = f^*(X)$ is the true conditional mean cost, $v = \hat f(X)$ its estimate, $z_1 = \pi_{\hat f}(X)$ the plug-in decision and $z_2 = \pi^*(X)$ an optimal decision: the excess cost of the plug-in decision at a single point is at most $2B$ times the estimation error there. It is the first step of the proof of Theorem 8.
--
--   **Formalization Note** The display is stated for arbitrary vectors and points of $\mathcal Z$, which is all the paper's display uses.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 8 (Appendix A.5), first display, p. 30

import Mathlib
import Definitions.Def_FastCLO_ETO_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace FastCLO.ETO

/-- **Proof of Theorem 8, first display** (Hu, Kallus, Mao, *Fast Rates for Contextual Linear
Optimization*, arXiv:2011.03030v3, Appendix A.5, p. 30): "By optimality of `π_f̂` with respect to
`f̂`, we have that `f*(X)ᵀ(π_f̂(X) − π*(X)) ≤ … ≤ 2B‖f*(X) − f̂(X)‖`."

Stated for one point: if `z₁` minimizes `vᵀz` over `Z` (the plug-in decision for the estimate
`v = f̂(x)`) and `z₂ ∈ Z` (the optimal decision `π*(x)`), then for the true cost `u = f*(x)`,
`uᵀ(z₁ − z₂) ≤ 2B‖u − v‖`.

Formalization Note: the display is formalized for arbitrary vectors `u, v` and points `z₁, z₂` of
`Z`, which is all the display uses; `B` is the norm bound of the polytope. -/
theorem pointwise_bound {d : ℕ} (P : Polytope d) (u v z₁ z₂ : FastCLO.ERM.Vec d)
    (hz₁ : z₁ ∈ P.Z) (hz₂ : z₂ ∈ P.Z) (hopt : ∀ z ∈ P.Z, ⟪v, z₁⟫_ℝ ≤ ⟪v, z⟫_ℝ) :
    ⟪u, z₁ - z₂⟫_ℝ ≤ 2 * P.B * ‖u - v‖ := by sorry

end FastCLO.ETO
