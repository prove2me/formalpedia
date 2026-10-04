-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_interval_restrict_iff_mconvex
-- name    : DiscreteConvex.MConvexFunctionsB.interval_restrict_iff_mconvex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:10:14.050031+00:00
-- url     : https://prove2.me/theorems/10e978f6-dfcd-422d-aaff-b1802cc58fe1
-- title:
--   Proposition 6.14 -- interval_restrict_iff_mconvex
-- statement:
--   **Proposition 6.14** (p.144). $f$ is M-convex if and only if $f_{[a,b]}$ is M-convex for every integer interval $[a,b]$ with nonempty domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.144, Proposition 6.14.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.144, Proposition 6.14

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_IntervalRestrict
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.144, Proposition 6.14, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.14 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.144). See the item's
`natural_language_statement` for the full statement. -/
theorem interval_restrict_iff_mconvex {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    MExchangeAxiom f ↔
      ∀ a b : V → WithBot (WithTop ℤ), (DomZ (IntervalRestrict f a b)).Nonempty →
        MExchangeAxiom (IntervalRestrict f a b) := by sorry

end DiscreteConvex.MConvexFunctionsB
