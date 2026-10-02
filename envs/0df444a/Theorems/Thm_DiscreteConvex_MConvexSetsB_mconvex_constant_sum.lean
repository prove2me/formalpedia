-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_mconvex_constant_sum
-- name    : DiscreteConvex.MConvexSetsB.mconvex_constant_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:30:53.078267+00:00
-- url     : https://prove2.me/theorems/103dfdc7-ed4f-491f-9b07-68319b3e8655
-- title:
--   Proposition 4.1 -- mconvex_constant_sum
-- statement:
--   **Proposition 4.1** (p.101). For an M-convex set $B$ we have $x(V) = y(V)$ for any $x, y \in B$: every point of an M-convex set has the same coordinate sum, so $B$ lies on a single hyperplane $\{x : x(V)=r\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, Proposition 4.1.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, Proposition 4.1

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, Proposition 4.1, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.1 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.101). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_constant_sum {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) :
    ∀ x ∈ B, ∀ y ∈ B, ∑ v, x v = ∑ v, y v := by sorry

end DiscreteConvex.MConvexSetsB
