-- Prove2me | Theorems.Thm_AnosovPlugs_hyperbolicSet_image_of_conjugacy
-- name    : AnosovPlugs.hyperbolicSet_image_of_conjugacy
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T01:17:21.394973+00:00
-- url     : https://prove2.me/theorems/aba57a91-f952-4188-b777-fc802b683458
-- title:
--   A hyperbolic set is carried to a hyperbolic set by a C¹ embedding that conjugates the flows near it
-- statement:
--   Let $M$ and $N$ be smooth 3-manifolds with boundary (modelled on the closed half-space), let $X$ be a vector field on $M$ and $Z$ a vector field on $N$, and let $i:M\to N$ be a C¹ map that is a topological embedding, has an injective derivative $Di_x$ at every point, and carries $X$ to $Z$:
--   $$ Di_x(X(x)) = Z(i(x))\quad\text{for every } x\in M. $$
--   A *hyperbolic set* of a vector field $X$ on a 3-manifold, with one-dimensional strong bundles, is (as in the mission) a set $\Lambda$ for which there are a continuous Riemannian metric $g$, subspaces $E^s(x), E^u(x)\subseteq T_xM$ for every $x\in M$, one-dimensional for $x\in\Lambda$, and constants $C>0$, $\lambda>0$ such that for every $x\in\Lambda$: $E^s(x)+\mathbb R\,X(x)+E^u(x)=T_xM$; $D(X^t)_x E^s(x)=E^s(X^t x)$ and $D(X^t)_x E^u(x)=E^u(X^t x)$ for every real $t$; and $\|D(X^t)_x v\|_g\le C e^{-\lambda t}\|v\|_g$ for $v\in E^s(x)$, $t\ge 0$, $\|D(X^{-t})_x v\|_g\le C e^{-\lambda t}\|v\|_g$ for $v\in E^u(x)$, $t\ge 0$. Here $X^t$ is the time-$t$ map of the (partial) flow of $X$. Let $\Lambda\subseteq M$ be a hyperbolic set of $X$ (with data $g, E^s, E^u, C, \lambda$ as above), and assume:
--
--   1. (invariance) $X^t(x)\in\Lambda$ for every $x\in\Lambda$ and every real $t$;
--   2. (interior) every point of $\Lambda$ is an interior point of $M$;
--   3. (openness along $\Lambda$) for every $x\in\Lambda$, the image $i(M)$ is a neighbourhood of $i(x)$ in $N$;
--   4. (local conjugacy) for every $x\in\Lambda$ and every real $t$ there is a neighbourhood $O$ of $x$ in $M$ with
--   $$ Z^t(i(y)) = i(X^t(y))\quad\text{for every } y\in O; $$
--   5. (comparable metrics) for every continuous Riemannian metric $g$ on $M$ there are a continuous Riemannian metric $g'$ on $N$ and constants $c_1, c_2>0$ with
--   $$ c_1\,\|v\|_{g,x}\ \le\ \|Di_x v\|_{g',i(x)}\ \le\ c_2\,\|v\|_{g,x}\quad\text{for every } x\in M,\ v\in T_xM. $$
--
--   Then $i(\Lambda)$ is a hyperbolic set of $Z$ (same definition, on $N$).
--
--   This is the transport of a hyperbolic structure through a C¹ embedding that conjugates the flows near $\Lambda$. In the proof of Proposition 1.1 it is the step that regards the hyperbolic structures of $\Lambda_X$ and $\Lambda_Y$ as hyperbolic structures of the glued field $Z$ on $W=U\sqcup_\varphi V$ (footnote 2: the differentiable structure of $W$ is compatible with those of $U$ and $V$ by restriction).
--
--   **Formalization Note** The time-$t$ map $X^t$ is the mission's `flowMap`: when some integral curve of $X$ through $x$ is defined on the closed time interval between $0$ and $t$, $X^t(x)$ is the value at time $t$ of a chosen such curve; otherwise $X^t(x)=x$. Nothing in the definition asserts that this choice is unique. The derivative $D(X^t)_x$ is Mathlib's `mfderiv`, which is $0$ where $X^t$ is not differentiable. The invariance in the definition of a hyperbolic set is quantified over all real $t$, and hypothesis 4 is stated with Mathlib's `∀ᶠ y in 𝓝 x`. The hyperbolic structure on $i(\Lambda)$ is the push-forward: $E^s(i(x))=Di_x(E^s(x))$, $E^u(i(x))=Di_x(E^u(x))$, with metric $g'$ and constants $C c_2/c_1$ and $\lambda$. Hypothesis 1 is used to show that $X^t$ is differentiable at the points of $\Lambda$ (from the invariance identity and $\dim E^s=1$), hypotheses 2 and 3 to transfer differentiability from $Z^t\circ i$ to $Z^t$ at $i(x)$. Hypothesis 3 also follows from hypothesis 2 and the injectivity of $Di_x$ by the inverse function theorem; it is kept as a hypothesis because the sketch obtains it from the companion statement `plugGluing_local_conjugacy`. No compactness is assumed; neither $X$ nor $Z$ is assumed to be C¹.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1, fourth and fifth sentences of the proof ('Then ΛZ is the union of ΛX, ΛY and the Z-orbit of the set φ_*(L^u_X) ∩ L^s_Y'; 'A classical consequence of the hyperbolic theory asserts that [...] the maximal invariant set on the vector field Z on U ⊔_φ V is hyperbolic'), which use without comment that ΛX and ΛY keep their hyperbolic structures in W; and footnote 2 of Section 1 (p. 2): the differentiable structure on W is compatible with those of U and V by restriction. The statement is the transport lemma behind these sentences, with the invariance of Λ, the interiority of Λ, the openness of i(M) along Λ, the local conjugacy and the comparability of metrics as hypotheses. Mathlib notions: mfderiv, Topology.IsEmbedding, Filter.Eventually; mission notions: IsHyperbolicSet, flowMap, RiemannianMetric3.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem hyperbolicSet_image_of_conjugacy
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (Λ : Set M) (hΛ : IsHyperbolicSet X Λ)
    (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (hΛinv : ∀ x ∈ Λ, ∀ t : ℝ, flowMap X t x ∈ Λ)
    (hint : ∀ x ∈ Λ, I3.IsInteriorPoint x)
    (hnhds : ∀ x ∈ Λ, range i ∈ 𝓝 (i x))
    (hconj : ∀ x ∈ Λ, ∀ t : ℝ, ∀ᶠ y in 𝓝 x, flowMap Z t (i y) = i (flowMap X t y))
    (hmetric : ∀ g : RiemannianMetric3 M, ∃ g' : RiemannianMetric3 N, ∃ c₁ c₂ : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧ ∀ (x : M) (v : TangentSpace I3 x),
        c₁ * g.norm x v ≤ g'.norm (i x) (mfderiv I3 I3 i x v) ∧
        g'.norm (i x) (mfderiv I3 I3 i x v) ≤ c₂ * g.norm x v) :
    IsHyperbolicSet Z (i '' Λ) := by sorry

end AnosovPlugs
