-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSets_exchange_axioms_equivalent
-- name    : DiscreteConvex.MConvexSets.exchange_axioms_equivalent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:20:45.353879+00:00
-- url     : https://prove2.me/theorems/7b394c78-f1d9-4b06-ac9d-6390bb539ae2
-- title:
--   Theorem 4.3 -- the four exchange axiom variants are equivalent
-- statement:
--   **Theorem 4.3** (p.103). Conditions (B-EXC[Z]), (B-EXCw[Z]), (B-EXC+[Z]), and (B-EXC-[Z]) are equivalent for a set $B \subseteq \mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Theorem 4.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Theorem 4.3

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomBWeak
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomBPlus
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomBMinus

namespace DiscreteConvex.MConvexSets

/-- Theorem 4.3 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.103). Conditions
`(B-EXC[Z])`, `(B-EXCw[Z])`, `(B-EXC+[Z])`, and `(B-EXC-[Z])` are equivalent for a set
`B ⊆ Zⱽ`. -/
theorem exchange_axioms_equivalent {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) :
    [ExchangeAxiomB B, ExchangeAxiomBWeak B, ExchangeAxiomBPlus B, ExchangeAxiomBMinus B].TFAE := by sorry

end DiscreteConvex.MConvexSets
