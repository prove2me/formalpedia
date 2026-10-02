-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_exchange_axiom_plus_equiv
-- name    : DiscreteConvex.MConvexSetsB.exchange_axiom_plus_equiv
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:31:27.676632+00:00
-- url     : https://prove2.me/theorems/12d73324-db41-488f-bb8c-07abe75dce3a
-- title:
--   Proposition 4.2 -- exchange_axiom_plus_equiv
-- statement:
--   **Proposition 4.2** (p.101). For a set $B \subseteq \mathbb Z^V$, (B-EXC[Z]) is equivalent to (B-EXC+[Z]): for $x,y \in B$ and $u \in \operatorname{supp}^+(x-y)$, there is $v \in \operatorname{supp}^-(x-y)$ with $y+\chi_u-\chi_v \in B$. The one-sided version, imposing the exchange condition only on the $y$-side, already forces the full two-sided axiom.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, Proposition 4.2.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, Proposition 4.2

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomBPlus

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, Proposition 4.2, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Proposition 4.2 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.101). See the item's
`natural_language_statement` for the full statement. -/
theorem exchange_axiom_plus_equiv {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) :
    ExchangeAxiomB B ↔ ExchangeAxiomBPlus B := by sorry

end DiscreteConvex.MConvexSetsB
