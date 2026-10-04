-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_hyperbolic_of_pieces_of_flows
-- name    : AnosovPlugs.plugGluing_hyperbolic_of_pieces_of_flows
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-03T20:58:07.019451+00:00
-- url     : https://prove2.me/theorems/ba8bea8e-d438-419b-9226-091687c78003
-- title:
--   Hyperbolicity of the maximal invariant set of a transverse plug gluing, given one metric, uniqueness of integral curves and C¹ local flows
-- statement:
--   Let $(U,X)$ and $(V,Y)$ be plugs: compact Hausdorff smooth 3-manifolds with boundary carrying nonsingular C¹ vector fields transverse to the boundary. Let $T^{out}\subseteq\partial^{out}U$ and $T^{in}\subseteq\partial^{in}V$ be unions of connected components of the exit and entrance boundaries, and let $\varphi:T^{out}\to T^{in}$ be a C¹ diffeomorphism (the mission's `IsBoundaryDiffeo`). Let $(W,Z,i_U,i_V)$ be a plug gluing (the mission's `IsPlugGluing`): $W$ is a compact Hausdorff smooth 3-manifold with boundary, $i_U:U\to W$ and $i_V:V\to W$ are C¹ embeddings with injective derivatives whose images cover $W$ and meet exactly along the seam $i_U(x)=i_V(\varphi(x))$, $x\in T^{out}$, and $Z$ is the vector field on $W$ with $Z\circ i_U=Di_U\circ X$ and $Z\circ i_V=Di_V\circ Y$. The field $Z$ is not assumed to be C¹. Assume in addition that $(U,X)$ and $(V,Y)$ are hyperbolic plugs (their maximal invariant sets $\Lambda_X$, $\Lambda_Y$ are hyperbolic sets), and that the gluing is transverse: at every point $p\in\varphi(L^u_X\cap T^{out})\cap L^s_Y$ the pushed exit leaf $\varphi_*(\text{leaf of } L^u_X)$ and the entrance leaf of $L^s_Y$ through $p$ are transverse curves in $\partial V$ (the mission's `CurvesTransverseAt`), where $L^u_X$ and $L^s_Y$ are the exit and entrance laminations. A set $\Lambda\subseteq M$ is a *hyperbolic set* of a vector field $X$ (the mission's `IsHyperbolicSet X Λ`) if there are a continuous Riemannian metric $g$, line fields $E^s$, $E^u$ on $\Lambda$ and constants $C>0$, $\lambda>0$ such that at every $x\in\Lambda$: $E^s_x\oplus\mathbb R X(x)\oplus E^u_x=T_xM$, the two line fields are invariant under the derivatives of the time-$t$ maps $\phi_t$ of the flow of $X$ for all $t\in\mathbb R$, and $\|D\phi_t(v)\|_g\le C e^{-\lambda t}\|v\|_g$ for $v\in E^s_x$, $t\ge0$, and $\|D\phi_{-t}(v)\|_g\le C e^{-\lambda t}\|v\|_g$ for $v\in E^u_x$, $t\ge0$. The time-$t$ map is the mission's `flowMap X t`, which sends $x$ to $\gamma(t)$ for a chosen integral curve $\gamma$ of $X$ on $[0,t]$ with $\gamma(0)=x$ when one exists, and to $x$ otherwise. Assume the maximal invariant set of $Z$ is described (the hypothesis `hΛ`, proved in the mission as `plugGluing_maxInvSet_subset` and `plugGluing_maxInvSet_superset`):
--   $$ \Lambda_Z = i_U(\Lambda_X)\ \cup\ i_V(\Lambda_Y)\ \cup\ \{\text{points of complete } Z\text{-orbits through } i_U(x),\ x\in L^u_X\cap T^{out},\ \varphi(x)\in L^s_Y\}. $$
--   Assume further the following. Each is the conclusion of another mission theorem, applied to the data above:
--   1. (one metric for both pieces) a continuous Riemannian metric $g$ on $W$ together with line fields and constants, separately for each piece, that make $i_U(\Lambda_X)$ and $i_V(\Lambda_Y)$ hyperbolic sets of $Z$ with respect to this same $g$ (`isHyperbolicSet_of_metric` applied to `plugGluing_pieces_hyperbolic`);
--   2. (uniqueness) integral curves of $Z$ on $[0,t]$ are determined by their starting point, for every $t$ (`plugGluing_integralCurveOn_unique`);
--   3. (C¹ local flows) at every interior point of $U$ the field $X$ has a local flow that is jointly C¹ in the initial point and the time, with the uniqueness clause of `exists_localFlow_contMDiff_of_isInteriorPoint`, and likewise for $Y$ on $V$.
--   Then the whole maximal invariant set is hyperbolic:
--   $$ \Lambda_Z \text{ is a hyperbolic set of } Z. $$
--
--   In words: this is the fifth sentence of the paper's proof of Proposition 1.1, which says that, by a classical consequence of the hyperbolic theory, the orbit of $\varphi_*(L^u_X)\cap L^s_Y$ inherits a hyperbolic structure, with the paper's description of the bundles at a connecting point $y\in T^{in}$: the stable bundle is $\mathbb R\,Y(y)\oplus T_yL^s_Y$ and the unstable bundle is $\mathbb R\,\varphi_*X(y)\oplus T_y\varphi_*(L^u_X)$, pushed into $W$ by $Di_V$. The expected proof: by hypothesis 2 the time-$t$ maps of $Z$ along a connecting orbit are given by that orbit, and the two pieces are flow invariant; the time-$t$ maps are C¹ along the connecting orbits: hypothesis 3 covers the interior of each piece, and near the seam a C¹ flow up to the boundary and the transversality of $X$ to $\partial U$ give a C¹ hitting time; the hyperbolic structures of the two pieces extend to cone fields on neighbourhoods; an unstable cone transported from $i_U(\Lambda_X)$ along a connecting orbit crosses the seam and, by the transversality hypothesis, lands inside the unstable cone of $i_V(\Lambda_Y)$ after a bounded transit time; the cone-field criterion with uniform constants (compactness of $\Lambda_Z$ and of the set of connecting points) gives the invariant splitting on all of $\Lambda_Z$; the unstable estimate is the same argument for $-Z$.
--
--   **Formalization Note** This theorem is the target `plugGluing_hyperbolic_of_pieces` with three added hypotheses, each the verbatim conclusion of a mission theorem: hypothesis 1 is the conclusion of `isHyperbolicSet_of_metric` (the body of `IsHyperbolicSet` with the metric fixed to $g$), hypothesis 2 is the conclusion of `plugGluing_integralCurveOn_unique`, and hypothesis 3 is the conclusion of `exists_localFlow_contMDiff_of_isInteriorPoint`, quantified over interior points of $U$ and of $V$. Two parts remain to be proved inside this theorem. The first part is the C¹ regularity of the time-$t$ maps of $Z$ across the seam: a C¹ flow of $X$ up to $T^{out}$ and of $Y$ from $T^{in}$, the C¹ hitting time of the seam, and the inverse function theorem for $i_U^{-1}$ and $i_V^{-1}$. Hypothesis 3 gives only local flows at interior points. The second part is the hyperbolic theory of transverse heteroclinic connections: cone fields, their transport across the seam, and uniform constants. Mathlib (at the pinned version) has neither part. The paper's description of the bundles at connecting points is not asserted, because `IsHyperbolicSet` is existential in the bundles. The field $Z$ is not assumed C¹; the time-$t$ map `flowMap Z t` is junk-valued where no integral curve exists.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Proof of Proposition 1.1, fifth sentence (arXiv v1 Section 3.1, p. 14; GT 2017 Section 4.1): the Z-orbit of φ_*(L^u_X) ∩ L^s_Y inherits a hyperbolic structure, 'a classical consequence of the hyperbolic theory' in the paper's words. Mission notions: IsHyperbolicSet, IsPlugGluing, CurvesTransverseAt, pushLeaf, exitLeaf, entranceLeaf, maxInvSet; companion theorems isHyperbolicSet_of_metric, plugGluing_integralCurveOn_unique, exists_localFlow_contMDiff_of_isInteriorPoint.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_hyperbolic_of_pieces_of_flows
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : IsHyperbolicPlug X) (hY : IsHyperbolicPlug Y)
    (Tout : Set U) (Tin : Set V) (hTout : IsUnionOfComponents Tout (outBoundary X))
    (hTin : IsUnionOfComponents Tin (inBoundary Y)) (φ : U → V)
    (hφ : IsBoundaryDiffeo φ Tout Tin)
    (htransv : ∀ p ∈ φ '' (exitLamination X ∩ Tout) ∩ entranceLamination Y,
      CurvesTransverseAt (pushLeaf φ Tout (exitLeaf X) p) (entranceLeaf Y p) p)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV)
    (hΛ : maxInvSet Z = iU '' maxInvSet X ∪ iV '' maxInvSet Y ∪
      {w | ∃ x ∈ exitLamination X ∩ Tout, φ x ∈ entranceLamination Y ∧
        ∃ γ : ℝ → W, γ 0 = iU x ∧ IsMIntegralCurve γ Z ∧ w ∈ range γ})
    (g : RiemannianMetric3 W)
    (hU : ∃ (Es Eu : (x : W) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ), 0 < C ∧ 0 < lam ∧
          ∀ x ∈ iU '' maxInvSet X,
            Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
            Es x ⊔ Submodule.span ℝ {Z x} ⊔ Eu x = ⊤ ∧
            (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Es (flowMap Z t x)) ∧
            (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Eu (flowMap Z t x)) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
              g.norm (flowMap Z t x) (mfderiv I3 I3 (flowMap Z t) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
              g.norm (flowMap Z (-t) x) (mfderiv I3 I3 (flowMap Z (-t)) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v))
    (hV : ∃ (Es Eu : (x : W) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ), 0 < C ∧ 0 < lam ∧
          ∀ x ∈ iV '' maxInvSet Y,
            Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
            Es x ⊔ Submodule.span ℝ {Z x} ⊔ Eu x = ⊤ ∧
            (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Es (flowMap Z t x)) ∧
            (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Eu (flowMap Z t x)) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
              g.norm (flowMap Z t x) (mfderiv I3 I3 (flowMap Z t) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
              g.norm (flowMap Z (-t) x) (mfderiv I3 I3 (flowMap Z (-t)) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v))
    (huniq : ∀ (γ γ' : ℝ → W) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
            γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    (hflowX : ∀ x₀ : U, I3.IsInteriorPoint x₀ →
      ∃ ε > (0 : ℝ), ∃ O : Set U, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : U → ℝ → U,
        (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
          ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
        ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p : U × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
        (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → U, η 0 = y →
          IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
          ∀ τ ∈ uIcc 0 h, η τ = α y τ))
    (hflowY : ∀ y₀ : V, I3.IsInteriorPoint y₀ →
      ∃ ε > (0 : ℝ), ∃ O : Set V, IsOpen O ∧ y₀ ∈ O ∧ ∃ α : V → ℝ → V,
        (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) Y (Icc (-ε) ε) ∧
          ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
        ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p : V × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
        (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → V, η 0 = y →
          IsMIntegralCurveOn η Y (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
          ∀ τ ∈ uIcc 0 h, η τ = α y τ)) :
    IsHyperbolicSet Z (maxInvSet Z) := by sorry

end AnosovPlugs
