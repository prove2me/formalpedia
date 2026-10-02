-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_polyhedral_mnat_convex_iff_exchange_R
-- name    : DiscreteConvex.MConvexFunctionsC.polyhedral_mnat_convex_iff_exchange_R
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:29.154361+00:00
-- url     : https://prove2.me/theorems/5484097c-7ead-4605-8455-6058810639d2
-- title:
--   Theorem 6.47 -- polyhedral_mnat_convex_iff_exchange_R
-- statement:
--   **Theorem 6.47** (p.162). For a polyhedral convex function $g:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ with nonempty effective domain, polyhedral M$^\natural$-convexity is equivalent to the direct real exchange axiom (M$^\natural$-EXC[R]).
--
--   **Formalization Note.** The book states a three-way equivalence, polyhedral M$^\natural$-convexity $\iff$ (M$^\natural$-EXC[R]) $\iff$ (M$^\natural$-EXC'[R]), where the third form uses one-sided directional derivatives (Eq. (6.73)-(6.74), citing Eq. (3.24)). Only the first equivalence is formalized here; the derivative-based reformulation needs its own directional-derivative infrastructure for possibly-infinite-valued convex functions, not otherwise needed by this chunk — see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162, Theorem 6.47.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162, Theorem 6.47

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvexR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsPolyhedralConvex

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.47 (p.162), first equivalence only (see `MODERATION_NOTES.md`). -/
theorem polyhedral_mnat_convex_iff_exchange_R (g : (V → ℝ) → WithTop ℝ) (hdom : (DomR g).Nonempty)
    (hpoly : IsPolyhedralConvex g) : MNaturalConvexR g ↔ MNatExchangeAxiomR g := by sorry

end DiscreteConvex.MConvexFunctionsC
