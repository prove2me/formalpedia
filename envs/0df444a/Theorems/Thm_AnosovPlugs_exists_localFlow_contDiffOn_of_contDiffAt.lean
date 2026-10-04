-- Prove2me | Theorems.Thm_AnosovPlugs_exists_localFlow_contDiffOn_of_contDiffAt
-- name    : AnosovPlugs.exists_localFlow_contDiffOn_of_contDiffAt
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T09:36:54.020432+00:00
-- url     : https://prove2.me/theorems/7271fd9f-20fd-49f2-bb72-f25417ceaa08
-- title:
--   A vector field that is C¹ at a point of a finite-dimensional space has a local flow there that is jointly C¹ and unique inside a ball
-- statement:
--   Let $E$ be a finite-dimensional real normed space, let $v:E\to E$ be a map that is of class C¹ at a point $z_0$ (that is, C¹ on a neighbourhood of $z_0$), and let $G$ be an open set that contains $z_0$. Then there are $\varepsilon>0$, $\rho>0$ and a map $\alpha_E:E\times\mathbb R\to E$ (a local flow) such that:
--   1. for every $z$ in the open ball $B(z_0,\rho)$: $\alpha_E(z,0)=z$, and for every $t\in[-\varepsilon,\varepsilon]$ the curve $s\mapsto\alpha_E(z,s)$ has derivative $v(\alpha_E(z,t))$ at $t$ and $\alpha_E(z,t)\in G$;
--   2. $\alpha_E$ is of class C¹ on $B(z_0,\rho)\times(-\varepsilon,\varepsilon)$;
--   3. (uniqueness inside the ball) for every $z\in B(z_0,\rho)$, every $h$ with $|h|\le\varepsilon$ and every curve $f:\mathbb R\to E$ with $f(0)=z$ that solves $f'=v(f)$ on the closed interval between $0$ and $h$ (derivative within the interval) and stays in $B(z_0,\rho)$ there, one has
--      $$ f(\tau)=\alpha_E(z,\tau)\quad\text{for all } \tau \text{ between } 0 \text{ and } h. $$
--
--   In words: near a point where it is C¹, a vector field on a finite-dimensional space has a local flow for a uniform short time that is jointly C¹ in the initial point and the time and is unique among solutions that stay in the ball. A general fact of analysis, not stated in the paper. In this mission it is a step in the proof of the companion theorem `exists_localFlow_contMDiff_of_isInteriorPoint`. That theorem says that the local flow of a C¹ vector field at an interior point is jointly C¹ in the initial point and the time. The proof of Proposition 1.1 (Section 3.1 of arXiv v1) uses it tacitly. There $E=\mathbb R^3$, $v$ is the vector field read in a chart, and $G$ is the interior of the chart target; the statement has the shape of the chart-level local flow in the solution of the proved theorem `exists_localFlow_of_isInteriorPoint`. Joint C¹ regularity replaces continuity in the initial point.
--
--   **Formalization Note** `ContDiffAt ℝ 1 v z₀` is Mathlib's pointwise C¹ notion, which gives C¹ on a neighbourhood. Clause 2 is `ContDiffOn ℝ 1 αE (Metric.ball z₀ ρ ×ˢ Ioo (-ε) ε)`. In clause 1 the derivative is two-sided (`HasDerivAt`) also at $t=\pm\varepsilon$, which holds because the flow exists on a larger interval. Finite dimension is used for a compactly supported cut-off of $v$, which makes the field globally Lipschitz so that the companion theorem `exists_flow_contDiffOn_of_lipschitz` applies. The closed interval between $0$ and $h$ is Mathlib's `uIcc 0 h`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Textbook ODE theory (local flow with differentiable dependence on initial conditions), not stated in the paper; used tacitly in the proof of Proposition 1.1. Mathlib notions: ContDiffAt, ContDiffOn, HasDerivAt, HasDerivWithinAt, ContDiffBump; companion theorem exists_flow_contDiffOn_of_lipschitz.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_localFlow_contDiffOn_of_contDiffAt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v : E → E} {z₀ : E} (hv : ContDiffAt ℝ 1 v z₀) {G : Set E} (hG : IsOpen G) (hz₀ : z₀ ∈ G) :
    ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ αE : E × ℝ → E,
      (∀ z ∈ Metric.ball z₀ ρ, αE (z, 0) = z ∧ ∀ t ∈ Icc (-ε) ε,
        HasDerivAt (fun s => αE (z, s)) (v (αE (z, t))) t ∧ αE (z, t) ∈ G) ∧
      ContDiffOn ℝ 1 αE (Metric.ball z₀ ρ ×ˢ Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball z₀ ρ, ∀ h : ℝ, |h| ≤ ε → ∀ f : ℝ → E, f 0 = z →
        (∀ τ ∈ uIcc 0 h, HasDerivWithinAt f (v (f τ)) (uIcc 0 h) τ) →
        (∀ τ ∈ uIcc 0 h, f τ ∈ Metric.ball z₀ ρ) → ∀ τ ∈ uIcc 0 h, f τ = αE (z, τ)) := by sorry

end AnosovPlugs
