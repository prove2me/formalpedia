-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_lovasz_extension_is_polyhedral_lconvex
-- name    : DiscreteConvex.LConvexFunctionsC.lovasz_extension_is_polyhedral_lconvex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:49:14.561277+00:00
-- url     : https://prove2.me/theorems/39b0028f-d02a-460e-aaec-29f4ec03b788
-- title:
--   Proposition 7.25 -- lovasz_extension_is_polyhedral_lconvex
-- statement:
--   **Proposition 7.25** (p.190-191). For $\rho\in S[\mathbb R]$ we have $\hat\rho\in L[\mathbb R\to\mathbb R]$: the Lov\'asz extension of a submodular set function is a polyhedral L-convex function.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading; its label starts a text line but the extractor evidently missed it. See `STATUS.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190-191, Proposition 7.25.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190-191, Proposition 7.25

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LovaszExtension
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.25 (p.190-191). The Lovász extension of a submodular set function is a
polyhedral L-convex function. -/
theorem lovasz_extension_is_polyhedral_lconvex (rho : Finset V → WithTop ℝ)
    (hrho : SubmodularSetFunction rho) :
    SBFR (LovaszExtension rho) ∧ TRFR (LovaszExtension rho) := by sorry

end DiscreteConvex.LConvexFunctionsC
