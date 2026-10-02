-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_mconvex_intersection_hull
-- name    : DiscreteConvex.MConvexSetsB.mconvex_intersection_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:31:29.827955+00:00
-- url     : https://prove2.me/theorems/22b20e71-63a1-4cea-ace7-89da0d8b93fc
-- title:
--   Theorem 4.22 -- mconvex_intersection_hull
-- statement:
--   **Theorem 4.22** (p.115). For M-convex sets $B_1, B_2 \subseteq \mathbb Z^V$, $\overline{B_1 \cap B_2} = \overline{B_1} \cap \overline{B_2}$: the convex hull of the intersection equals the intersection of the convex hulls — a stronger integrality statement than the disjointness-preservation of Theorem 4.21 (an empty intersection of the convex hulls forces an empty intersection of the sets themselves).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, Theorem 4.22.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.115, Theorem 4.22

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.115, Theorem 4.22, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.22 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.115). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_intersection_hull {V : Type*} [Fintype V] [DecidableEq V] (B1 B2 : Set (V → ℤ))
    (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2) (hB1ne : B1.Nonempty)
    (hB2ne : B2.Nonempty) :
    convexHull ℝ (IntEmbed (B1 ∩ B2)) = convexHull ℝ (IntEmbed B1) ∩ convexHull ℝ (IntEmbed B2) := by sorry

end DiscreteConvex.MConvexSetsB
