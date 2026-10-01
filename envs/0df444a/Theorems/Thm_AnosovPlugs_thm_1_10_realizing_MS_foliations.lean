-- Prove2me | Theorems.Thm_AnosovPlugs_thm_1_10_realizing_MS_foliations
-- name    : AnosovPlugs.thm_1_10_realizing_MS_foliations
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T09:41:05.860429+00:00
-- url     : https://prove2.me/theorems/c24a77e2-2376-4ec3-aebd-44690f02e5a4
-- title:
--   Theorem 1.10 (Béguin–Bonatti–Yu): every MS foliation is the entrance foliation of a transitive hyperbolic attractor
-- statement:
--   For every MS foliation $\mathcal F$ on a closed orientable surface $S$, there exist an orientable transitive attracting hyperbolic plug $(U,X)$ and a homeomorphism $h:\partial^{in}U\to S$ such that
--   $$h_*\big(L^s(U,X)\big)=\mathcal F.$$
--
--   **Formalization Note** The foliation is given by a topological foliated atlas; $h_*(L^s)=\mathcal F$ is expressed leafwise: $h$ maps each leaf of the entrance lamination onto the leaf of $\mathcal F$ through the image point. "Transitive" means that the maximal invariant set has a dense orbit.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1845, Theorem 1.10 (proof in §9)

import Mathlib
import Definitions.Def_AnosovPlugs_Surfaces

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem thm_1_10_realizing_MS_foliations
    {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S] (hS : IsOrientableSurface S)
    (A : Set (OpenPartialHomeomorph S (ℝ × ℝ))) (hA : IsMSFoliation A) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : ChartedSpace (EuclideanHalfSpace 3) U)
      (_ : IsManifold I3 ∞ U) (_ : T2Space U) (_ : CompactSpace U), IsOrientable U ∧
      ∃ X : (x : U) → TangentSpace I3 x, IsAttractingPlug X ∧ IsHyperbolicPlug X ∧
        (∃ x ∈ maxInvSet X, maxInvSet X ⊆ closure (range fun t : ℝ => flowMap X t x)) ∧
        ∃ h : inBoundary X ≃ₜ S, ∀ p : inBoundary X,
          (fun q : inBoundary X => h q) '' {q | (q : U) ∈ entranceLeaf X p} =
            foliationLeaf A (h p) := by sorry

end AnosovPlugs
