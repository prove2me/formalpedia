-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_local_exchange_iff_exchange
-- name    : DiscreteConvex.MConvexFunctionsB.local_exchange_iff_exchange
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:10:06.396712+00:00
-- url     : https://prove2.me/theorems/e637fa60-bf9a-47e5-940f-5ac81dfd1acb
-- title:
--   Theorem 6.4 -- local_exchange_iff_exchange
-- statement:
--   **Theorem 6.4** (p.136). If $\operatorname{dom} f$ is an M-convex set, then (M-EXC[Z]) is equivalent to the local exchange axiom (M-EXCloc[Z]), which requires the exchange inequality only for $x,y$ at $\ell^1$-distance exactly $4$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.136, Theorem 6.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.136, Theorem 6.4

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiomLoc
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.136, Theorem 6.4, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Theorem 6.4 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.136). See the item's
`natural_language_statement` for the full statement. -/
theorem local_exchange_iff_exchange {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hdom : ExchangeAxiomB (DomZ f)) :
    MExchangeAxiom f ↔ MExchangeAxiomLoc f := by sorry

end DiscreteConvex.MConvexFunctionsB
