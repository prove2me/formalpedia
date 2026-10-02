-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSets_hole_free_lconvex
-- name    : DiscreteConvex.LConvexSets.hole_free_lconvex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:36:52.03726+00:00
-- url     : https://prove2.me/theorems/3d4da4fe-b97e-4ad2-8340-40b7f15748af
-- title:
--   Theorem 5.2 -- L-convex sets are hole free
-- statement:
--   **Theorem 5.2** (p.123). An L-convex set is hole free: $D = \bar D \cap \mathbb Z^V$ for an L-convex set $D \subseteq \mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.123, Theorem 5.2.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.123, Theorem 5.2

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSets_ConvexClosureSet

namespace DiscreteConvex.LConvexSets

/-- Theorem 5.2 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.123). An L-convex set is
hole free: `D = D̄ ∩ Zⱽ` for an L-convex set `D ⊆ Zⱽ`. -/
theorem hole_free_lconvex {V : Type*} [Fintype V] [DecidableEq V] (D : Set (V → ℤ))
    (hD : LConvexSet D) :
    ∀ p : V → ℤ, p ∈ D ↔ (fun v => (p v : ℝ)) ∈ ConvexClosureSet D := by sorry

end DiscreteConvex.LConvexSets
