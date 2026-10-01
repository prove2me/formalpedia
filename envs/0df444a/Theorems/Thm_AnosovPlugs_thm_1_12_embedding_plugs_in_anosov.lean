-- Prove2me | Theorems.Thm_AnosovPlugs_thm_1_12_embedding_plugs_in_anosov
-- name    : AnosovPlugs.thm_1_12_embedding_plugs_in_anosov
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:15:05.509196+00:00
-- url     : https://prove2.me/theorems/f9e6ffa0-bfe2-4670-b5f1-f67180e0cbd1
-- title:
--   Theorem 1.12 (Béguin–Bonatti–Yu): hyperbolic plugs with filling MS laminations embed in Anosov flows
-- statement:
--   Consider a hyperbolic plug with filling MS laminations $(U_0,X_0)$.
--
--   1. Up to changing $(U_0,X_0)$ by a topological equivalence, one can find an Anosov vector field $X$ on a closed orientable three-manifold $M$ and an embedding $\theta:U_0\hookrightarrow M$ with $\theta_*X_0=X$ (on $\theta(U_0)$).
--   2. Moreover, if the maximal invariant set of $(U_0,X_0)$ contains neither attractors nor repellers, the construction can be done so that $X$ is transitive.
--
--   **Formalization Note** Item 1 is formalized as: there are a closed orientable $M$, an Anosov $X$ on $M$, a C¹ embedding $\iota:U_0\to M$ and the pulled-back field $Y=\iota^*X$ on $U_0$ ($D\iota(Y)=X\circ\iota$), transverse to $\partial U_0$, with $Y$ topologically equivalent to $X_0$. Connectedness of $M$ is not claimed in the conclusion.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1845, Theorem 1.12 (proof in §9)

import Mathlib
import Definitions.Def_AnosovPlugs_Laminations

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem thm_1_12_embedding_plugs_in_anosov {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (X₀ : (x : U) → TangentSpace I3 x) (hX₀ : IsFillingHyperbolicPlug X₀) :
    (∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M)
        (_ : IsManifold I3 ∞ M) (_ : T2Space M) (_ : CompactSpace M)
        (_ : BoundarylessManifold I3 M), IsOrientable M ∧
      ∃ X : (x : M) → TangentSpace I3 x, IsAnosov X ∧
        ∃ (ι : U → M) (Y : (x : U) → TangentSpace I3 x),
          ContMDiff I3 I3 1 ι ∧ Topology.IsEmbedding ι ∧
          (∀ x, Function.Injective (mfderiv I3 I3 ι x)) ∧
          (∀ x, mfderiv I3 I3 ι x (Y x) = X (ι x)) ∧ IsNonsingularTransverse Y ∧
          TopologicallyEquivalent X₀ Y) ∧
    (NoAttractorNorRepeller X₀ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M)
        (_ : IsManifold I3 ∞ M) (_ : T2Space M) (_ : CompactSpace M)
        (_ : BoundarylessManifold I3 M), IsOrientable M ∧
      ∃ X : (x : M) → TangentSpace I3 x, IsAnosov X ∧ IsTransitiveFlow X ∧
        ∃ (ι : U → M) (Y : (x : U) → TangentSpace I3 x),
          ContMDiff I3 I3 1 ι ∧ Topology.IsEmbedding ι ∧
          (∀ x, Function.Injective (mfderiv I3 I3 ι x)) ∧
          (∀ x, mfderiv I3 I3 ι x (Y x) = X (ι x)) ∧ IsNonsingularTransverse Y ∧
          TopologicallyEquivalent X₀ Y) := by sorry

end AnosovPlugs
