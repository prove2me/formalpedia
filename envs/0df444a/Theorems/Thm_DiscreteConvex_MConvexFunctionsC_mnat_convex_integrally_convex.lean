-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mnat_convex_integrally_convex
-- name    : DiscreteConvex.MConvexFunctionsC.mnat_convex_integrally_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:45:05.97591+00:00
-- url     : https://prove2.me/theorems/bd32421d-81da-4ea4-9199-37b5f8eefbda
-- title:
--   Theorem 6.42 -- mnat_convex_integrally_convex
-- statement:
--   **Theorem 6.42** (p.159). An M$^\natural$-convex function is integrally convex. In particular, an M$^\natural$-convex function is convex extensible.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.159, Theorem 6.42.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.159, Theorem 6.42

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsIntegrallyConvexFunction

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.42 (p.159). -/
theorem mnat_convex_integrally_convex (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    IsIntegrallyConvexFunction f ∧ ConvexExtensible f := by sorry

end DiscreteConvex.MConvexFunctionsC
