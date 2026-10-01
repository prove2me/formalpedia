-- Prove2me | Theorems.Thm_AnosovPlugs_lemma_3_27_self_gluing_exists
-- name    : AnosovPlugs.lemma_3_27_self_gluing_exists
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T02:57:12.606988+00:00
-- url     : https://prove2.me/theorems/93b1a27f-bec0-4e36-a635-409d636e336e
-- title:
--   Lemma 3.27 (Béguin–Bonatti–Yu), self-gluing case: the glued manifold U/φ exists
-- statement:
--   Let $(U,X)$ be a plug on a compact 3-manifold and $\varphi:\partial^{out}U\to\partial^{in}U$ a diffeomorphism. Then the quotient $U/\varphi$ carries a smooth structure making it a closed 3-manifold $N$, such that the quotient map $q:U\to N$ is a C¹ immersion and $X$ induces a vector field $Z$ on $N$:
--   $$Dq_x(X(x)) = Z(q(x))\quad\text{for all } x\in U.$$
--
--   This guarantees that the universally quantified conclusions about "the vector field induced on $U/\varphi$" (Theorem 1.5, Proposition 1.6) are not vacuous.
--
--   **Formalization Note** Only the case used by Theorem 1.5 (gluing the whole exit boundary to the whole entrance boundary of one plug) is stated. The induced field $Z$ is not asserted to be C¹.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, p. 1862, Lemma 3.27 (special case $V_1=V_2=U$, $S_1=\partial^{out}U$, $S_2=\partial^{in}U$) and §1.3, p. 1841

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem lemma_3_27_self_gluing_exists {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (X : (x : U) → TangentSpace I3 x) (φ : U → U) (hX : IsPlug X)
    (hφ : IsBoundaryDiffeo φ (outBoundary X) (inBoundary X)) :
    ∃ (N : Type) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanHalfSpace 3) N)
      (_ : IsManifold I3 ∞ N) (_ : T2Space N) (_ : CompactSpace N)
      (_ : BoundarylessManifold I3 N) (Z : (y : N) → TangentSpace I3 y) (q : U → N),
      IsSelfGluing X φ Z q := by sorry

end AnosovPlugs
