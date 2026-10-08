-- Prove2me | Theorems.Thm_AnosovPlugs_flowMap_contMDiffOn_of_localSteps
-- name    : AnosovPlugs.flowMap_contMDiffOn_of_localSteps
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T20:35:34.534976+00:00
-- url     : https://prove2.me/theorems/855151c8-4f98-4620-bb74-f671986fec5e
-- title:
--   If a vector field with unique integral curves has C¹ short-time flow maps near every point of an orbit segment, its time-t map is C¹ near the starting point
-- statement:
--   Let $N$ be a smooth 3-manifold with boundary (modelled on the closed half-space) and let $Z$ be a vector field on $N$; no regularity of $Z$ is assumed. An *integral curve of a vector field $Z$ on a manifold $N$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to N$ whose derivative within $S$ at every $u\in S$ is $Z(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). A vector field $Z$ on a 3-manifold $N$ has *local C¹ step maps at a point* $p$ if there are $\varepsilon>0$ and an open neighbourhood $O$ of $p$ such that for every $h$ with $|h|\le\varepsilon$ there is a map $f_h:N\to N$ of class C¹ on $O$ with this property: every $y\in O$ is the starting point of an integral curve $\eta$ of $Z$ on $[0,h]$ with $\eta(h)=f_h(y)$. We write $\phi^Z_t$ for the time-$t$ map of $Z$, the mission's `flowMap Z t`: it sends $y$ to $\gamma(t)$ for a chosen integral curve $\gamma$ of $Z$ on $[0,t]$ with $\gamma(0)=y$ when one exists (the mission's `FlowDefined Z y t`), and to $y$ otherwise. Assume:
--   1. (uniqueness) for every $t$, two integral curves of $Z$ on $[0,t]$ with the same starting point are equal on $[0,t]$;
--   2. $\gamma$ is an integral curve of $Z$ on $[0,t]$, and $Z$ has local C¹ step maps at $\gamma(s)$ for every $s\in[0,t]$.
--   Then there is an open neighbourhood $O$ of $\gamma(0)$ such that the orbit of every $y\in O$ is defined on $[0,t]$ and
--   $$ \phi^Z_t \text{ is of class } C^1 \text{ on } O. $$
--
--   In words: if short-time flow maps are C¹ near every point of a compact orbit segment, then the time-$t$ map is C¹ near the starting point. The proof covers the segment by finitely many step neighbourhoods (Lebesgue number), composes the step maps, and uses uniqueness to identify the composition with the time-$t$ map. It is a step of the mission's proof of the C¹ regularity that the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14) takes for granted. There $Z$ is the glued field, which is not known to be C¹ across the seam; the step maps come from `localSteps_of_embedding` and `plugGluing_localSteps_seam`.
--
--   **Formalization Note** The step maps are phrased with integral curves and not with `flowMap`, because `flowMap` is junk-valued where no integral curve exists. The interval $[0,t]$ is `uIcc 0 t`, so both time directions are covered. No Hausdorff and no compactness hypothesis is assumed. C¹ on $O$ is `ContMDiffOn I3 I3 1 f O`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). General fact (composition of local flow maps along a compact orbit segment), used tacitly in the proof of Proposition 1.1 (arXiv v1 Section 3.1). Mathlib notion: IsMIntegralCurveOn; mission notions: flowMap, FlowDefined.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem flowMap_contMDiffOn_of_localSteps
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (Z : (w : N) → TangentSpace I3 w)
    (huniq : ∀ (γ γ' : ℝ → N) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
        γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    (γ : ℝ → N) (t : ℝ) (hγ : IsMIntegralCurveOn γ Z (uIcc 0 t))
    (hloc : ∀ s ∈ uIcc 0 t,
      ∃ ε > (0 : ℝ), ∃ O : Set N, IsOpen O ∧ γ s ∈ O ∧ ∀ h : ℝ, |h| ≤ ε → ∃ f : N → N,
        ContMDiffOn I3 I3 1 f O ∧
        ∀ y ∈ O, ∃ η : ℝ → N, η 0 = y ∧ IsMIntegralCurveOn η Z (uIcc 0 h) ∧ η h = f y) :
    ∃ O : Set N, IsOpen O ∧ γ 0 ∈ O ∧
      (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O := by sorry

end AnosovPlugs
