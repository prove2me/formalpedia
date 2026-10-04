-- Prove2me | Theorems.Thm_AnosovPlugs_isHyperbolicSet_of_metric
-- name    : AnosovPlugs.isHyperbolicSet_of_metric
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T20:57:05.486978+00:00
-- url     : https://prove2.me/theorems/70baa314-d516-4c0c-b5de-fbb143005535
-- title:
--   On a compact 3-manifold, a hyperbolic set is hyperbolic with respect to every continuous Riemannian metric
-- statement:
--   Let $M$ be a compact smooth 3-manifold with boundary (modelled on the closed half-space), let $X$ be a vector field on $M$ and let $\Lambda\subseteq M$ be a hyperbolic set of $X$. A set $\Lambda\subseteq M$ is a *hyperbolic set* of a vector field $X$ (the mission's `IsHyperbolicSet X Λ`) if there are a continuous Riemannian metric $g$, line fields $E^s$, $E^u$ on $\Lambda$ and constants $C>0$, $\lambda>0$ such that at every $x\in\Lambda$: $E^s_x\oplus\mathbb R X(x)\oplus E^u_x=T_xM$, the two line fields are invariant under the derivatives of the time-$t$ maps $\phi_t$ of the flow of $X$ for all $t\in\mathbb R$, and $\|D\phi_t(v)\|_g\le C e^{-\lambda t}\|v\|_g$ for $v\in E^s_x$, $t\ge0$, and $\|D\phi_{-t}(v)\|_g\le C e^{-\lambda t}\|v\|_g$ for $v\in E^u_x$, $t\ge0$. The time-$t$ map is the mission's `flowMap X t`, which sends $x$ to $\gamma(t)$ for a chosen integral curve $\gamma$ of $X$ on $[0,t]$ with $\gamma(0)=x$ when one exists, and to $x$ otherwise. A *continuous Riemannian metric* $g$ on a 3-manifold $M$ is a continuously varying inner product $g_x$ on the tangent spaces $T_xM$ (Mathlib's `Bundle.ContinuousRiemannianMetric` on the tangent bundle; the mission's `RiemannianMetric3`), with norm $\|v\|_{g,x}=\sqrt{g_x(v,v)}$. Then for every continuous Riemannian metric $g$ on $M$ there are line fields $E^s,E^u$ and constants $C>0$, $\lambda>0$ that satisfy the hyperbolicity conditions for $\Lambda$ with respect to $g$:
--   $$ \forall g\ \exists E^s, E^u, C>0, \lambda>0:\quad \Lambda \text{ is hyperbolic for } X \text{ with respect to } (g, E^s, E^u, C, \lambda). $$
--
--   In words: on a compact manifold, hyperbolicity of a set does not depend on the choice of the continuous Riemannian metric. Only the constant $C$ changes. The proof compares the given metric with $g$ along the identity map (companion theorem `comparable_of_metrics` with $i=\mathrm{id}$): $c_1\|v\|_{g_0}\le\|v\|_g\le c_2\|v\|_{g_0}$ for all tangent vectors, and replaces $C$ by $C c_2/c_1$. It is used in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14; GT 2017 Section 4.1). The proof of Proposition 1.1 needs the hyperbolic structures of the two pieces $i_U(\Lambda_X)$ and $i_V(\Lambda_Y)$ in one metric. The paper does not state this step.
--
--   **Formalization Note** The conclusion is the body of the mission's `IsHyperbolicSet X Λ` with the metric fixed to the given $g$ instead of existentially quantified; the exponent $\lambda$ may be kept. Compactness of $M$ is what makes the comparison constants uniform. The norm is the mission's `RiemannianMetric3.norm`, that is $\sqrt{g_x(v,v)}$.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). General fact (change of the continuous metric on a compact manifold), used tacitly in the proof of Proposition 1.1 (arXiv v1 Section 3.1, GT 2017 Section 4.1). Mission notions: IsHyperbolicSet, RiemannianMetric3, RiemannianMetric3.norm; companion theorem comparable_of_metrics.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem isHyperbolicSet_of_metric
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [CompactSpace M]
    (X : (x : M) → TangentSpace I3 x) (Λ : Set M) (hΛ : IsHyperbolicSet X Λ)
    (g : RiemannianMetric3 M) :
    ∃ (Es Eu : (x : M) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ), 0 < C ∧ 0 < lam ∧
      ∀ x ∈ Λ,
        Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
        Es x ⊔ Submodule.span ℝ {X x} ⊔ Eu x = ⊤ ∧
        (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap X t) x).toLinearMap = Es (flowMap X t x)) ∧
        (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap X t) x).toLinearMap = Eu (flowMap X t x)) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
          g.norm (flowMap X t x) (mfderiv I3 I3 (flowMap X t) x v)
            ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
          g.norm (flowMap X (-t) x) (mfderiv I3 I3 (flowMap X (-t)) x v)
            ≤ C * Real.exp (-lam * t) * g.norm x v) := by sorry

end AnosovPlugs
