-- Prove2me | Theorems.Thm_AnosovPlugs_gluing_theorem
-- name    : AnosovPlugs.gluing_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T02:59:55.152302+00:00
-- url     : https://prove2.me/theorems/51dea1e5-730c-49ea-8fff-c7d9b5ef1c92
-- title:
--   Theorem 1.5 (Béguin–Bonatti–Yu): gluing a hyperbolic plug to itself yields an Anosov flow
-- statement:
--   Let $(U,X)$ be a hyperbolic plug with filling MS laminations (a compact 3-manifold $U$ with boundary, a nonsingular C¹ vector field $X$ transverse to $\partial U$ whose maximal invariant set $\Lambda$ is hyperbolic, and whose entrance and exit laminations $L^s_X\subset\partial^{in}U$, $L^u_X\subset\partial^{out}U$ are filling). Assume that $\Lambda$ contains neither attractors nor repellers, and let $\varphi:\partial^{out}U\to\partial^{in}U$ be a strongly transverse gluing diffeomorphism.
--
--   Then there exist a hyperbolic plug $(U,Y)$ with filling MS laminations and a strongly transverse gluing diffeomorphism $\psi:\partial^{out}U\to\partial^{in}U$ such that
--
--   1. $(U,X,\varphi)$ and $(U,Y,\psi)$ are strongly isotopic, and
--   2. the vector field $Z$ induced by $Y$ on the closed manifold $U/\psi$ is Anosov:
--   $$Z \text{ on } U/\psi \ \text{ is Anosov}.$$
--
--   This is the paper's main gluing theorem: it allows one to build Anosov flows on closed 3-manifolds by gluing the exit boundary of a hyperbolic plug to its entrance boundary, after a strong isotopy.
--
--   **Formalization Note** The closed manifold $U/\psi$ is not built as a quotient type: the conclusion is stated for every closed smooth 3-manifold $N$ with a surjective C¹ immersion $q:U\to N$ realising the identification $x\sim\psi(x)$ and pushing $Y$ to $Z$ (such $N$ exist by Lemma 3.27, a separate milestone). "Anosov" is stated as hyperbolicity of the whole manifold for the flow of $Z$ (the induced field need not be C¹ for every compatible smooth structure).
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1842, Theorem 1.5

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem gluing_theorem {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (X : (x : U) → TangentSpace I3 x) (φ : U → U)
    (hX : IsFillingHyperbolicPlug X) (hXnoAR : NoAttractorNorRepeller X)
    (hφ : IsStronglyTransverseGluing X φ) :
    ∃ (Y : (x : U) → TangentSpace I3 x) (ψ : U → U),
      IsFillingHyperbolicPlug Y ∧ IsStronglyTransverseGluing Y ψ ∧ StronglyIsotopic X φ Y ψ ∧
      ∀ (N : Type) [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
        [IsManifold I3 ∞ N] [T2Space N] [CompactSpace N] [BoundarylessManifold I3 N]
        (Z : (y : N) → TangentSpace I3 y) (q : U → N),
        IsSelfGluing Y ψ Z q → IsHyperbolicSet Z univ := by sorry

end AnosovPlugs
