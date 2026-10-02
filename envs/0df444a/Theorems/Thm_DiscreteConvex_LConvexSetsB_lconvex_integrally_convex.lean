-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSetsB_lconvex_integrally_convex
-- name    : DiscreteConvex.LConvexSetsB.lconvex_integrally_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:50:00.531673+00:00
-- url     : https://prove2.me/theorems/8c3e71e8-e292-4b34-9e66-dea76fc0a45d
-- title:
--   Theorem 5.10 -- lconvex_integrally_convex
-- statement:
--   **Theorem 5.10** (p.127-128). GOAL. For an L-convex set $D \subseteq \mathbb Z^V$,
--
--   $$\overline D = \{p \in \mathbb R^V : \lfloor p\rfloor + \chi_{U_i(p)} \in D\ (i=0,1,\ldots,m)\},$$
--
--   where $U_i(p)$ are the level sets of the fractional part of $p$ (Eq. (5.11)-(5.12)). Hence an L-convex set is integrally convex: every point of its convex hull is already a convex combination of finitely many nearby integer points of $D$ (its own integral neighborhood), an explicit witness rather than an abstract existence claim.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127-128, Theorem 5.10, Eq. (5.11)-(5.12).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127-128, Theorem 5.10

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracSortedValues
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracVec
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracLevelSet
import Definitions.Def_DiscreteConvex_LConvexSetsB_NeighborVec
import Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegrallyConvex
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntegralNeighborhood

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.127-128, Theorem 5.10, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- Theorem 5.10 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.127-128). See the item's
`natural_language_statement` for the full statement. -/
theorem lconvex_integrally_convex {V : Type*} [Fintype V] [DecidableEq V] (D : Set (V → ℤ))
    (hD : LConvexSet D) :
    (convexHull ℝ (IntEmbed D) =
      {p : V → ℝ | ∀ i ≤ (FracSortedValues p).length, NeighborVec p i ∈ D}) ∧
    IsIntegrallyConvex D := by sorry

end DiscreteConvex.LConvexSetsB
