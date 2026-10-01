-- Prove2me | Theorems.Thm_AnosovPlugs_thm_1_13_many_anosov_flows
-- name    : AnosovPlugs.thm_1_13_many_anosov_flows
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:53:00.807654+00:00
-- url     : https://prove2.me/theorems/e5a51c3a-ecbe-4472-a1de-9a228d4a4e53
-- title:
--   Theorem 1.13 (Béguin–Bonatti–Yu): 3-manifolds with arbitrarily many transitive Anosov flows
-- statement:
--   For any $n\ge1$ there is a closed orientable three-manifold $M$ supporting at least $n$ transitive Anosov vector fields $Z_1,\dots,Z_n$ which are pairwise topologically nonequivalent:
--   $$ i\neq j\ \Longrightarrow\ Z_i \not\simeq Z_j .$$
--
--   **Formalization Note** $M$ is connected, compact, Hausdorff, boundaryless and orientable; the vector fields are indexed by $\mathrm{Fin}\,n$.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1846, Theorem 1.13 (proof in §10)

import Mathlib
import Definitions.Def_AnosovPlugs_Hyperbolic

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem thm_1_13_many_anosov_flows (n : ℕ) (hn : 1 ≤ n) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M)
      (_ : IsManifold I3 ∞ M) (_ : T2Space M) (_ : CompactSpace M) (_ : ConnectedSpace M)
      (_ : BoundarylessManifold I3 M), IsOrientable M ∧
      ∃ Z : Fin n → (x : M) → TangentSpace I3 x,
        (∀ i, IsAnosov (Z i) ∧ IsTransitiveFlow (Z i)) ∧
        ∀ i j, i ≠ j → ¬ TopologicallyEquivalent (Z i) (Z j) := by sorry

end AnosovPlugs
