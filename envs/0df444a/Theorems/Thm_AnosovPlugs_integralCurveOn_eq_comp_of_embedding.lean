-- Prove2me | Theorems.Thm_AnosovPlugs_integralCurveOn_eq_comp_of_embedding
-- name    : AnosovPlugs.integralCurveOn_eq_comp_of_embedding
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T08:59:16.924101+00:00
-- url     : https://prove2.me/theorems/ac62d55a-84a0-45cb-a1c5-11dc2fe010d0
-- title:
--   An integral curve of an i-related field that starts at the image of the starting point of an interior integral curve is the image of that curve
-- statement:
--   Let $M$ and $N$ be Hausdorff smooth 3-manifolds with boundary (modelled on the closed half-space), let $X$ be a C¹ vector field on $M$ and $Z$ a vector field on $N$, and let $i:M\to N$ be a C¹ map that is a topological embedding, has an injective derivative at every point, and carries $X$ to $Z$:
--   $$ Di_x(X(x)) = Z(i(x))\quad\text{for every } x\in M. $$
--   An *integral curve of $X$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to M$ whose derivative within $S$ at every $u\in S$ is $X(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). Let $\delta$ be an integral curve of $X$ on $[0,t]$ all of whose points $\delta(s)$, $s\in[0,t]$, are interior points of $M$, and let $\gamma$ be an integral curve of $Z$ on $[0,t]$ with $\gamma(0)=i(\delta(0))$. Then
--   $$ \gamma(s)=i(\delta(s))\quad\text{for every } s\in[0,t]. $$
--
--   In words: an integral curve of $Z$ that starts at $i(\delta(0))$, where $\delta$ is an integral curve of $X$ through interior points of $M$, equals $i\circ\delta$ on the whole time interval; in particular it does not leave $i(M)$. The intended proof lifts $\gamma$ through $i$ on short time spans (the companion lemma `integralCurve_lift_of_embedding`, proved earlier in this mission), uses that $i(M)$ is a neighbourhood of each $i(\delta(s))$ (`range_mem_nhds_of_isInteriorPoint`) and the uniqueness statement `isMIntegralCurveOn_uIcc_eq`, and extends the agreement over the whole interval by a closed-and-open argument. A general fact, not stated in the paper; it is one of the facts behind footnote 2 of Section 1 (p. 2 of arXiv v1: the differentiable structure on W is compatible with those of U and V by restriction) and behind the fourth and fifth sentences of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), which state without proof that Λ_Z contains Λ_X and Λ_Y (through the inclusions) and use, without comment, that Λ_X and Λ_Y are hyperbolic sets of Z. In the proof of `plugGluing_local_conjugacy` it identifies the integral curve of $Z$ chosen by the time-$t$ map at $i_U(y)$ with the image of the orbit of $y$ under $X$.
--
--   **Formalization Note** $Z$ is not assumed to be C¹ or even continuous; its curves are controlled only through the embedding. The Hausdorff hypotheses are used for the closedness of the set of agreement times and in the uniqueness statement. No compactness is assumed.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact, not stated in the paper; it is one of the facts behind footnote 2 of Section 1 (p. 2 of arXiv v1: the differentiable structure on W is compatible with those of U and V by restriction) and behind the fourth and fifth sentences of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), which state without proof that Λ_Z contains Λ_X and Λ_Y (through the inclusions) and use, without comment, that Λ_X and Λ_Y are hyperbolic sets of Z. Mathlib notions: IsMIntegralCurveOn, Topology.IsEmbedding, mfderiv; mission notion: IsC1VectorField; companion statements integralCurve_lift_of_embedding, range_mem_nhds_of_isInteriorPoint, isMIntegralCurveOn_uIcc_eq.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem integralCurveOn_eq_comp_of_embedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [T2Space N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hX : IsC1VectorField X) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (δ : ℝ → M) (t : ℝ) (hδ : IsMIntegralCurveOn δ X (uIcc 0 t))
    (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (δ s))
    (γ : ℝ → N) (hγ : IsMIntegralCurveOn γ Z (uIcc 0 t)) (h0 : γ 0 = i (δ 0)) :
    ∀ s ∈ uIcc 0 t, γ s = i (δ s) := by sorry

end AnosovPlugs
