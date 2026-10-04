-- Prove2me | Theorems.Thm_AnosovPlugs_isMIntegralCurveOn_uIcc_eq
-- name    : AnosovPlugs.isMIntegralCurveOn_uIcc_eq
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T08:59:02.877959+00:00
-- url     : https://prove2.me/theorems/99b1e36b-46e8-4424-bbf3-b23033b6c1f6
-- title:
--   Uniqueness of integral curves of a C¹ vector field on a closed interval from an endpoint, through interior points
-- statement:
--   Let $M$ be a Hausdorff smooth 3-manifold with boundary (modelled on the closed half-space) and let $X$ be a C¹ vector field on $M$. An *integral curve of $X$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to M$ whose derivative within $S$ at every $u\in S$ is $X(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). Let $\gamma$ and $\gamma'$ be integral curves of $X$ on $[0,t]$ with $\gamma'(0)=\gamma(0)$, and assume that every point $\gamma(s)$, $s\in[0,t]$, is an interior point of $M$. Then
--   $$ \gamma'(s)=\gamma(s)\quad\text{for every } s\in[0,t]. $$
--
--   In words: uniqueness of integral curves of a C¹ vector field on a closed time interval, starting from the common endpoint $0$, when one of the two curves runs through interior points. A general fact, not stated in the paper; it is one of the facts behind footnote 2 of Section 1 (p. 2 of arXiv v1: the differentiable structure on W is compatible with those of U and V by restriction) and behind the fourth and fifth sentences of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), which state without proof that Λ_Z contains Λ_X and Λ_Y (through the inclusions) and use, without comment, that Λ_X and Λ_Y are hyperbolic sets of Z. It generalizes the companion statement `flowMap_eq_of_isMIntegralCurve` (which needs a complete first curve) and is used in the proof of `plugGluing_local_conjugacy` to identify the integral curve chosen by the mission's time-$t$ map with a given curve.
--
--   **Formalization Note** The interior hypothesis is on $\gamma$ only, as in Mathlib's uniqueness theorem `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`, which this statement extends from open intervals with an interior common point to closed intervals with the common point at an endpoint (by gluing a short-time integral curve on the other side of $0$). No compactness is assumed. The Hausdorff hypothesis is a hypothesis of `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff` and also closes the far endpoint of the interval; it cannot be dropped (on $\mathbb R^3$ with a doubled point, two integral curves of a constant field through the two copies of the point agree at time $0$ and differ later). C¹ is the mission's `IsC1VectorField`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact, not stated in the paper; it is one of the facts behind footnote 2 of Section 1 (p. 2 of arXiv v1: the differentiable structure on W is compatible with those of U and V by restriction) and behind the fourth and fifth sentences of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), which state without proof that Λ_Z contains Λ_X and Λ_Y (through the inclusions) and use, without comment, that Λ_X and Λ_Y are hyperbolic sets of Z. Mathlib notions: IsMIntegralCurveOn, isMIntegralCurveOn_Ioo_eqOn_of_contMDiff, exists_isMIntegralCurveAt_of_contMDiffAt; mission notion: IsC1VectorField.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem isMIntegralCurveOn_uIcc_eq
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ γ' : ℝ → M) (t : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc 0 t)) (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ s))
    (hγ' : IsMIntegralCurveOn γ' X (uIcc 0 t)) (h0 : γ' 0 = γ 0) :
    ∀ s ∈ uIcc 0 t, γ' s = γ s := by sorry

end AnosovPlugs
