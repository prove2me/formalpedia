-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mnat_convex_satisfies_swgs
-- name    : DiscreteConvex.MConvexFunctionsC.mnat_convex_satisfies_swgs
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:39:26.19405+00:00
-- url     : https://prove2.me/theorems/fc1709db-d37b-47ac-b312-178bd47fca24
-- title:
--   Proposition 6.35 -- mnat_convex_satisfies_swgs
-- statement:
--   **Proposition 6.35** (p.155). An M$^\natural$-convex function $f \in M^\natural[\mathbb Z\to\mathbb R]$ satisfies (M$^\natural$-SWGS[Z]), the stepwise gross substitutes property.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.155, Proposition 6.35.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.155, Proposition 6.35

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatSWGS

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.35 (p.155). -/
theorem mnat_convex_satisfies_swgs (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    MNatSWGS f := by sorry

end DiscreteConvex.MConvexFunctionsC
