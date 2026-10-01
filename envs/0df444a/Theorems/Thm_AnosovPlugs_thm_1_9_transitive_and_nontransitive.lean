-- Prove2me | Theorems.Thm_AnosovPlugs_thm_1_9_transitive_and_nontransitive
-- name    : AnosovPlugs.thm_1_9_transitive_and_nontransitive
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T03:36:38.368984+00:00
-- url     : https://prove2.me/theorems/e1b8cd02-ab9b-45d8-8bb1-6589a08221f6
-- title:
--   Theorem 1.9 (Béguin–Bonatti–Yu): a 3-manifold with both transitive and nontransitive Anosov flows
-- statement:
--   There exists a closed orientable three-manifold $M$ supporting both a transitive Anosov vector field $X$ and a nontransitive Anosov vector field $Y$:
--   $$\exists M,\ \exists X,Y:\quad X,Y \text{ Anosov},\ X \text{ transitive},\ Y \text{ not transitive}.$$
--
--   This answers a question of A. Katok.
--
--   **Formalization Note** Closed means compact, Hausdorff, boundaryless and (by the standing convention of the field) connected; vector fields are C¹.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1844, Theorem 1.9 (proof in §8)

import Mathlib
import Definitions.Def_AnosovPlugs_Hyperbolic

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem thm_1_9_transitive_and_nontransitive :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M)
      (_ : IsManifold I3 ∞ M) (_ : T2Space M) (_ : CompactSpace M) (_ : ConnectedSpace M)
      (_ : BoundarylessManifold I3 M), IsOrientable M ∧
      ∃ X Y : (x : M) → TangentSpace I3 x,
        IsAnosov X ∧ IsTransitiveFlow X ∧ IsAnosov Y ∧ ¬ IsTransitiveFlow Y := by sorry

end AnosovPlugs
