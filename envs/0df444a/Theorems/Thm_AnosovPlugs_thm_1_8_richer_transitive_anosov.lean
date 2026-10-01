-- Prove2me | Theorems.Thm_AnosovPlugs_thm_1_8_richer_transitive_anosov
-- name    : AnosovPlugs.thm_1_8_richer_transitive_anosov
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T03:25:04.563255+00:00
-- url     : https://prove2.me/theorems/509a7ee2-2856-4f33-bca5-192125771742
-- title:
--   Theorem 1.8 (Béguin–Bonatti–Yu): every transitive Anosov flow is a factor of a richer one
-- statement:
--   Given any transitive Anosov vector field $X$ on a closed (orientable) three-manifold $M$, there exists a transitive Anosov vector field $Z$ on a closed (orientable) three-manifold $N$ such that the dynamics of $Z$ is richer than the dynamics of $X$: there exist a compact set $\Lambda\subset N$ invariant under the flow of $Z$ and a continuous onto map $\pi:\Lambda\to M$ with
--   $$\pi\circ Z^t = X^t\circ\pi\qquad\text{for every } t\in\mathbb R.$$
--
--   **Formalization Note** The paper prints $\pi\circ X^t=Z^t\circ\pi$, which does not type-check since $\pi:\Lambda\to M$; the semiconjugacy $\pi\circ Z^t=X^t\circ\pi$ is formalized. The parenthetical "(orientable)" is formalized as: if $M$ is orientable then $N$ can be taken orientable.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1843, Theorem 1.8 (proof in §8)

import Mathlib
import Definitions.Def_AnosovPlugs_Hyperbolic

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem thm_1_8_richer_transitive_anosov
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [BoundarylessManifold I3 M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsAnosov X) (hXtr : IsTransitiveFlow X) :
    ∃ (N : Type) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanHalfSpace 3) N)
      (_ : IsManifold I3 ∞ N) (_ : T2Space N) (_ : CompactSpace N)
      (_ : BoundarylessManifold I3 N),
      (IsOrientable M → IsOrientable N) ∧
      ∃ Z : (y : N) → TangentSpace I3 y, IsAnosov Z ∧ IsTransitiveFlow Z ∧
        ∃ (Λ : Set N) (π : N → M), IsCompact Λ ∧ (∀ y ∈ Λ, ∀ t : ℝ, flowMap Z t y ∈ Λ) ∧
          ContinuousOn π Λ ∧ π '' Λ = univ ∧
          ∀ y ∈ Λ, ∀ t : ℝ, π (flowMap Z t y) = flowMap X t (π y) := by sorry

end AnosovPlugs
