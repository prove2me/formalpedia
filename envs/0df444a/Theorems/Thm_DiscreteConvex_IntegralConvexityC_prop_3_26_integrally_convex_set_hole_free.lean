-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityC_prop_3_26_integrally_convex_set_hole_free
-- name    : DiscreteConvex.IntegralConvexityC.prop_3_26_integrally_convex_set_hole_free
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:14:28.488488+00:00
-- url     : https://prove2.me/theorems/0f6de1d0-d362-44dc-b428-fb2c3366fd76
-- title:
--   Proposition 3.26 -- an integrally convex set is hole free
-- statement:
--   $S=\bar S\cap\mathbb Z^n$ for an integrally convex set $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.96, Proposition 3.26.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.96, Proposition 3.26

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_HoleFree

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.96, Proposition 3.26, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.26.** `S = S̄ ∩ Zⁿ` for an integrally convex set `S` (an integrally convex
set is hole free). -/
theorem prop_3_26_integrally_convex_set_hole_free {n : ℕ} (S : Set (Fin n → ℤ))
    (hS : IntegrallyConvexSet S) : HoleFree S := by sorry

end DiscreteConvex.IntegralConvexityC
