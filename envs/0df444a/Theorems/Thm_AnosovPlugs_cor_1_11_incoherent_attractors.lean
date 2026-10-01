-- Prove2me | Theorems.Thm_AnosovPlugs_cor_1_11_incoherent_attractors
-- name    : AnosovPlugs.cor_1_11_incoherent_attractors
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:01:10.066985+00:00
-- url     : https://prove2.me/theorems/9d3bc6ac-f90d-43f4-bc86-81a5e12cce66
-- title:
--   Corollary 1.11 (Béguin–Bonatti–Yu): incoherent transitive hyperbolic attractors exist
-- statement:
--   There exist incoherent transitive hyperbolic attractors on orientable manifolds: there is an orientable attracting hyperbolic plug $(U,X)$ whose maximal invariant set is transitive, and two compact leaves $\gamma_1,\gamma_2$ of $L^s(U,X)$ in the same connected component of $\partial^{in}U$ which, equipped with their contracting orientations, are not freely homotopic.
--
--   **Formalization Note** Contracting orientations are loop parametrisations along which the holonomy of the entrance foliation (on a C¹ transverse arc) is a contraction; free homotopy is taken in $\partial^{in}U$.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1845, Corollary 1.11 and the definition of incoherence preceding it

import Mathlib
import Definitions.Def_AnosovPlugs_Surfaces

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem cor_1_11_incoherent_attractors :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : ChartedSpace (EuclideanHalfSpace 3) U)
      (_ : IsManifold I3 ∞ U) (_ : T2Space U) (_ : CompactSpace U), IsOrientable U ∧
      ∃ X : (x : U) → TangentSpace I3 x, IsAttractingPlug X ∧ IsHyperbolicPlug X ∧
        (∃ x ∈ maxInvSet X, maxInvSet X ⊆ closure (range fun t : ℝ => flowMap X t x)) ∧
        IsIncoherent X := by sorry

end AnosovPlugs
