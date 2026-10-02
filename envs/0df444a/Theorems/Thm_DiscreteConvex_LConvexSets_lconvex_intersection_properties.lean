-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSets_lconvex_intersection_properties
-- name    : DiscreteConvex.LConvexSets.lconvex_intersection_properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:37:03.695978+00:00
-- url     : https://prove2.me/theorems/44ffc1c3-2a1a-49ec-bd43-fc6a76ae51da
-- title:
--   Theorem 5.7 -- L-convex sets are closed under intersection
-- statement:
--   **Theorem 5.7**, parts (1) and (4) (p.125). For L-convex sets $D_1, D_2 \subseteq \mathbb Z^V$: (1) $\bar D_1 \cap \bar D_2 = \overline{D_1 \cap D_2}$ (convexity in intersection); (4) if $D_1 \cap D_2$ is nonempty, it is again an L-convex set.
--
--   **Formalization Note.** The book's parts (2)-(3) additionally describe $D_1 \cap D_2$ via a specific representation $D_i = D(\gamma_i) \cap \mathbb Z^V$ and characterize nonemptiness via absence of a negative cycle in the associated graph; these are not needed by Theorem 5.9's own statement (only by its proof) and are omitted from this milestone as a scope decision.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.125, Theorem 5.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.125, Theorem 5.7

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSets_ConvexClosureSet

namespace DiscreteConvex.LConvexSets

/-- Theorem 5.7, parts (1) and (4) (Murota, *Discrete Convex Analysis*, SIAM 2003, p.125). For
L-convex sets `D1, D2 ⊆ Zⱽ`: (1) `D̄1 ∩ D̄2 = (D1 ∩ D2)‾` (convexity in intersection); (4) if
`D1 ∩ D2` is nonempty, it is again an L-convex set. -/
theorem lconvex_intersection_properties {V : Type*} [Fintype V] [DecidableEq V]
    (D1 D2 : Set (V → ℤ)) (hD1 : LConvexSet D1) (hD2 : LConvexSet D2) :
    ConvexClosureSet D1 ∩ ConvexClosureSet D2 = ConvexClosureSet (D1 ∩ D2) ∧
      ((D1 ∩ D2).Nonempty → LConvexSet (D1 ∩ D2)) := by sorry

end DiscreteConvex.LConvexSets
