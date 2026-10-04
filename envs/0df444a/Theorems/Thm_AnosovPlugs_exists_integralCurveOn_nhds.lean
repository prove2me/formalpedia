-- Prove2me | Theorems.Thm_AnosovPlugs_exists_integralCurveOn_nhds
-- name    : AnosovPlugs.exists_integralCurveOn_nhds
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T08:59:13.017513+00:00
-- url     : https://prove2.me/theorems/3ec7a7f0-61d7-4273-86f3-9ebe059ae29c
-- title:
--   Integral curves through interior points on a compact time interval persist for nearby initial points
-- statement:
--   Let $M$ be a smooth 3-manifold with boundary (modelled on the closed half-space) and let $X$ be a C¹ vector field on $M$. An *integral curve of $X$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to M$ whose derivative within $S$ at every $u\in S$ is $X(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). Let $\gamma$ be an integral curve of $X$ on $[0,t]$ all of whose points $\gamma(s)$, $s\in[0,t]$, are interior points of $M$. Then every point $y$ in some neighbourhood of $\gamma(0)$ is the starting point of an integral curve of $X$ on $[0,t]$ through interior points: for all $y$ near $\gamma(0)$,
--   $$ \exists\,\gamma':\mathbb R\to M,\qquad \gamma'(0)=y,\quad \gamma' \text{ is an integral curve of } X \text{ on } [0,t],\quad \gamma'(s) \text{ is an interior point of } M \text{ (not on } \partial M\text{) for } s\in[0,t]. $$
--
--   In words: orbits that stay in the interior of $M$ for a compact span of time persist for nearby initial points. This is the continuous dependence of solutions of a C¹ ordinary differential equation on initial conditions (continuation plus the Gronwall estimate in charts), restricted to what the formal development needs. A general fact, not stated in the paper; it is one of the facts behind footnote 2 of Section 1 (p. 2 of arXiv v1: the differentiable structure on W is compatible with those of U and V by restriction) and behind the fourth and fifth sentences of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), which state without proof that Λ_Z contains Λ_X and Λ_Y (through the inclusions) and use, without comment, that Λ_X and Λ_Y are hyperbolic sets of Z. In the proof of the companion statement `plugGluing_local_conjugacy` it provides, for $y$ near a point of $\Lambda_X$, an orbit of $X$ that stays in the interior of $U$ up to time $t$, so that the time-$t$ map of the glued field $Z$ at $i_U(y)$ can be computed inside $U$.
--
--   **Formalization Note** No uniqueness is asserted and no Hausdorff or compactness hypothesis is assumed. Mathlib (at the pinned version) has short-time existence at interior points (`exists_isMIntegralCurveAt_of_contMDiffAt`) and, on boundaryless manifolds, global existence from a uniform existence time (`exists_isMIntegralCurve_of_isMIntegralCurveOn`); it has no continuous dependence on initial conditions, so existence on a prescribed compact time interval for nearby initial points is not available, which is why this statement is left open. C¹ is the mission's `IsC1VectorField` (the section $x\mapsto(x,X(x))$ of the tangent bundle is C¹). The conclusion is stated with Mathlib's `∀ᶠ y in 𝓝 (γ 0)`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact, not stated in the paper; it is one of the facts behind footnote 2 of Section 1 (p. 2 of arXiv v1: the differentiable structure on W is compatible with those of U and V by restriction) and behind the fourth and fifth sentences of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), which state without proof that Λ_Z contains Λ_X and Λ_Y (through the inclusions) and use, without comment, that Λ_X and Λ_Y are hyperbolic sets of Z. Standard ODE theory (continuous dependence on initial conditions). Mathlib notions: IsMIntegralCurveOn, ModelWithCorners.IsInteriorPoint, Filter.Eventually; mission notion: IsC1VectorField.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_integralCurveOn_nhds
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ : ℝ → M) (t : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc 0 t)) (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ s)) :
    ∀ᶠ y in 𝓝 (γ 0), ∃ γ' : ℝ → M, γ' 0 = y ∧ IsMIntegralCurveOn γ' X (uIcc 0 t) ∧
      ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ' s) := by sorry

end AnosovPlugs
