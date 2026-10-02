-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mconvex_extension_is_polyhedral_mconvex
-- name    : DiscreteConvex.MConvexFunctionsC.mconvex_extension_is_polyhedral_mconvex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:39:59.303314+00:00
-- url     : https://prove2.me/theorems/6fd72f83-91e0-4190-82ec-a6b3c156383c
-- title:
--   Theorem 6.45 -- mconvex_extension_is_polyhedral_mconvex
-- statement:
--   **Theorem 6.45** (p.161). The convex extension $\bar f$ of an M-convex function $f\in M[\mathbb Z\to\mathbb R]$ on the integer lattice is a polyhedral M-convex function (i.e. $\bar f \in M[\mathbb R\to\mathbb R]$), provided $\bar f$ is polyhedral.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, Theorem 6.45.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, Theorem 6.45

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsPolyhedralConvex

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.45 (p.161). -/
theorem mconvex_extension_is_polyhedral_mconvex (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hpoly : IsPolyhedralConvex (ConvexClosureVal f)) : MExchangeAxiomR (ConvexClosureVal f) := by sorry

end DiscreteConvex.MConvexFunctionsC
