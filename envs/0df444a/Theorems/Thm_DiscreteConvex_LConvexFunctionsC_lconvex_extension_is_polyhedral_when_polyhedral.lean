-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_lconvex_extension_is_polyhedral_when_polyhedral
-- name    : DiscreteConvex.LConvexFunctionsC.lconvex_extension_is_polyhedral_when_polyhedral
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:49:42.505701+00:00
-- url     : https://prove2.me/theorems/f2b4de83-a34a-4c5c-8419-33135059d03e
-- title:
--   Theorem 7.26 -- lconvex_extension_is_polyhedral_when_polyhedral
-- statement:
--   **Theorem 7.26** (p.191). The convex extension $\bar g$ of an L-convex function $g\in L[\mathbb Z\to\mathbb R]$ on the integer lattice is a polyhedral L-convex function, i.e. $\bar g\in L[\mathbb R\to\mathbb R]$, provided that $\bar g$ is polyhedral.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, Theorem 7.26.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, Theorem 7.26

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedralConvex

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.26 (p.191). The convex extension of an L-convex function, when polyhedral, is
polyhedral L-convex. -/
theorem lconvex_extension_is_polyhedral_when_polyhedral (g : (V → ℤ) → WithTop ℝ)
    (hg : SBF g ∧ TRF g) (hpoly : IsPolyhedralConvex (fun p => ConvexClosureVal g p)) :
    SBFR (fun p => ConvexClosureVal g p) ∧ TRFR (fun p => ConvexClosureVal g p) := by sorry

end DiscreteConvex.LConvexFunctionsC
