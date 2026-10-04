-- Prove2me | Theorems.Thm_AnosovPlugs_integralCurve_lift_of_embedding
-- name    : AnosovPlugs.integralCurve_lift_of_embedding
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-02T22:56:16.103394+00:00
-- url     : https://prove2.me/theorems/7184df88-3004-4f80-875e-c3645dea58bb
-- title:
--   Integral curves lift through a C¹ embedding with injective derivative that carries one vector field to another
-- statement:
--   Let $M$ and $N$ be smooth 3-manifolds with boundary, modelled on the closed half-space, let $X$ be a vector field on $M$ and $Z$ a vector field on $N$, and let $i:M\to N$ be a C¹ map that is a topological embedding, has an injective derivative at every point, and carries $X$ to $Z$:
--   $$ Di_x(X(x)) = Z(i(x))\quad\text{for every } x\in M. $$
--   Let $\gamma:\mathbb R\to N$ be an integral curve of $Z$ on a set of times $s\subseteq\mathbb R$ (at every $t\in s$ the curve has derivative $Z(\gamma(t))$ within $s$), and assume that $s$ is nonempty and that $\gamma(t)$ lies in the image $i(M)$ for every $t\in s$. Then $\gamma$ lifts through $i$ to an integral curve of $X$: there is a curve $\delta:\mathbb R\to M$ with
--   $$ i(\delta(t))=\gamma(t)\ \text{ for every } t\in s,\qquad\text{and}\qquad \delta \text{ is an integral curve of } X \text{ on } s. $$
--
--   This is a general fact about C¹ immersions that are embeddings; it is the step that lets one read the dynamics of a glued vector field $Z$ on $W=U\sqcup_\varphi V$ inside the pieces $U$ and $V$. Footnote 2 of the paper (the differentiable structure on $W$ is compatible with those of $U$ and $V$ by restriction) gives the setting in which the inclusions of $U$ and $V$ into $W$ are C¹ embeddings; the lemma is used implicitly in the proof of Proposition 1.1.
--
--   **Formalization Note** The curve $\gamma$ is a total function on $\mathbb R$; its values outside $s$ are irrelevant. "Integral curve on $s$" is Mathlib's `IsMIntegralCurveOn`, with one-sided derivatives at the endpoints of $s$ when $s$ is an interval; the lemma is stated for an arbitrary set of times $s$. No compactness and no regularity of $Z$ beyond the identity $Di(X)=Z\circ i$ is assumed. The set of times $s$ is assumed nonempty: when $s$ is empty the conclusion still asks for a curve $\delta:\mathbb R\to M$, and no such curve exists if $M$ is empty.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact about C¹ immersions, not stated in the paper. Footnote 2 of Section 1 (p. 2; the differentiable structure on W is compatible with those of U and V by restriction) gives the setting; the lemma is used implicitly in the fourth sentence of the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14; Section 4.1 of the published version): 'Then Λ_Z is the union of Λ_X, Λ_Y and the Z-orbit of the set φ_*(L^u_X) ∩ L^s_Y.' Mathlib notions: IsMIntegralCurveOn, Topology.IsEmbedding, mfderiv.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem integralCurve_lift_of_embedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (γ : ℝ → N) (s : Set ℝ) (hγ : IsMIntegralCurveOn γ Z s) (hrange : ∀ t ∈ s, γ t ∈ range i)
    (hs : s.Nonempty) :
    ∃ δ : ℝ → M, (∀ t ∈ s, i (δ t) = γ t) ∧ IsMIntegralCurveOn δ X s := by sorry

end AnosovPlugs
