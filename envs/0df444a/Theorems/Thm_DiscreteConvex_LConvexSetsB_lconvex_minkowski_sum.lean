-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSetsB_lconvex_minkowski_sum
-- name    : DiscreteConvex.LConvexSetsB.lconvex_minkowski_sum
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:44:57.452132+00:00
-- url     : https://prove2.me/theorems/6aa0e041-2176-4afd-9d71-2524717e042d
-- title:
--   Theorem 5.8 -- lconvex_minkowski_sum
-- statement:
--   **Theorem 5.8** (p.126). For L-convex sets $D_1, D_2 \subseteq \mathbb Z^V$, $\overline{D_1+D_2} = \overline{D_1}+\overline{D_2}$: the convex hull of the Minkowski sum equals the Minkowski sum of the convex hulls ("convexity in Minkowski sum"). Unlike the M-convex case (Theorem 4.23(3)), the Minkowski sum of two L-convex sets need **not** itself be L-convex (Note 5.11 gives an explicit counterexample), so this theorem states only the closure identity, not L-convexity of $D_1+D_2$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.126, Theorem 5.8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.126, Theorem 5.8

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntEmbed
open scoped Pointwise

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.126, Theorem 5.8, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- Theorem 5.8 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.126). See the item's
`natural_language_statement` for the full statement. -/
theorem lconvex_minkowski_sum {V : Type*} [Fintype V] [DecidableEq V] (D1 D2 : Set (V → ℤ))
    (hD1 : LConvexSet D1) (hD2 : LConvexSet D2) :
    convexHull ℝ (IntEmbed (D1 + D2)) = convexHull ℝ (IntEmbed D1) + convexHull ℝ (IntEmbed D2) := by sorry

end DiscreteConvex.LConvexSetsB
