-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_mconvex_and_mnat_domains
-- name    : DiscreteConvex.MConvexFunctionsB.mconvex_and_mnat_domains
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:11:34.85431+00:00
-- url     : https://prove2.me/theorems/2d204c55-acd3-4a40-b68a-f9c77b8c7922
-- title:
--   Proposition 6.7 -- mconvex_and_mnat_domains
-- statement:
--   **Proposition 6.7** (p.138). (1) The effective domain of an M-convex function is an M-convex set. (2) The effective domain of an M$^\natural$-convex function is an M$^\natural$-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.138, Proposition 6.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.138, Proposition 6.7

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNatConvexSet

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.138, Proposition 6.7, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.7 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.138). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_and_mnat_domains {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    (MExchangeAxiom f → ExchangeAxiomB (DomZ f)) ∧
    (MNaturalConvex f → MNatConvexSet (DomZ f)) := by sorry

end DiscreteConvex.MConvexFunctionsB
