-- Prove2me | Theorems.Thm_AnosovPlugs_thm_1_15_infinitely_many_transverse_tori
-- name    : AnosovPlugs.thm_1_15_infinitely_many_transverse_tori
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:59:35.885714+00:00
-- url     : https://prove2.me/theorems/93323671-f219-4a1e-b699-b3c9b49f5c35
-- title:
--   Theorem 1.15 (Béguin–Bonatti–Yu): a transitive Anosov flow with infinitely many nonisotopic transverse tori
-- statement:
--   There exists a transitive Anosov vector field $Z$ on a closed orientable three-manifold $M$ such that there exist infinitely many pairwise nonisotopic tori embedded in $M$ and transverse to $Z$:
--   $$\exists (T_n)_{n\in\mathbb N}:\ T_n \pitchfork Z,\quad m\neq n\Rightarrow T_m \not\sim_{\text{isotopy}} T_n.$$
--
--   **Formalization Note** Tori are C¹ embeddings of $S^1\times S^1$; isotopy is C¹ isotopy through embedded tori, up to reparametrisation of the final torus.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1847, Theorem 1.15 (proof in §11)

import Mathlib
import Definitions.Def_AnosovPlugs_Tori
import Definitions.Def_AnosovPlugs_Hyperbolic

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem thm_1_15_infinitely_many_transverse_tori :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M)
      (_ : IsManifold I3 ∞ M) (_ : T2Space M) (_ : CompactSpace M) (_ : ConnectedSpace M)
      (_ : BoundarylessManifold I3 M), IsOrientable M ∧
      ∃ Z : (x : M) → TangentSpace I3 x, IsAnosov Z ∧ IsTransitiveFlow Z ∧
        ∃ f : ℕ → Circle × Circle → M, (∀ n, IsTransverseTorus Z (f n)) ∧
          ∀ m n, m ≠ n → ¬ ToriIsotopic (f m) (f n) := by sorry

end AnosovPlugs
