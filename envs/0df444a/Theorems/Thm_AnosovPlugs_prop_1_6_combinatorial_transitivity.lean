-- Prove2me | Theorems.Thm_AnosovPlugs_prop_1_6_combinatorial_transitivity
-- name    : AnosovPlugs.prop_1_6_combinatorial_transitivity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T03:10:44.232897+00:00
-- url     : https://prove2.me/theorems/c17e2d1b-1382-4e8b-9d23-0ac6f3c0c11e
-- title:
--   Proposition 1.6 (Béguin–Bonatti–Yu): combinatorial transitivity implies transitivity of the glued Anosov flow
-- statement:
--   Under the hypotheses of Theorem 1.5, if $(U,X,\varphi)$ is combinatorially transitive (the oriented graph on the basic pieces of $X$, with edges given by intersections $W^u(\Lambda_i)\cap W^s(\Lambda_j)$ inside $U$ or across the gluing $\varphi$, is strongly connected), then the Anosov vector field $Z$ produced by Theorem 1.5 is transitive:
--   $$ Z \text{ is Anosov and transitive on } U/\psi.$$
--
--   **Formalization Note** Stated as a strengthening of the conclusion of Theorem 1.5: the plug $(U,Y)$ and gluing map $\psi$ can be chosen so that, in addition, every induced field $Z$ on any realisation of $U/\psi$ is hyperbolic on the whole manifold and has a dense orbit.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1843, Proposition 1.6 (proof in §6.3)

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem prop_1_6_combinatorial_transitivity {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (X : (x : U) → TangentSpace I3 x) (φ : U → U)
    (hX : IsFillingHyperbolicPlug X) (hXnoAR : NoAttractorNorRepeller X)
    (hφ : IsStronglyTransverseGluing X φ) (hcomb : IsCombinatoriallyTransitive X φ) :
    ∃ (Y : (x : U) → TangentSpace I3 x) (ψ : U → U),
      IsFillingHyperbolicPlug Y ∧ IsStronglyTransverseGluing Y ψ ∧ StronglyIsotopic X φ Y ψ ∧
      ∀ (N : Type) [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
        [IsManifold I3 ∞ N] [T2Space N] [CompactSpace N] [BoundarylessManifold I3 N]
        (Z : (y : N) → TangentSpace I3 y) (q : U → N),
        IsSelfGluing Y ψ Z q → IsHyperbolicSet Z univ ∧ IsTransitiveFlow Z := by sorry

end AnosovPlugs
