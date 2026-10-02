-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mnat_convex_satisfies_gs
-- name    : DiscreteConvex.MConvexFunctionsC.mnat_convex_satisfies_gs
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:39:08.164838+00:00
-- url     : https://prove2.me/theorems/f6a00a06-7d5e-4d9c-b109-c362732d88ea
-- title:
--   Proposition 6.33 -- mnat_convex_satisfies_gs
-- statement:
--   **Proposition 6.33** (p.154). An M$^\natural$-convex function $f \in M^\natural[\mathbb Z\to\mathbb R]$ satisfies (M$^\natural$-GS[Z]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.154, Proposition 6.33.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.154, Proposition 6.33

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatGS

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.33 (p.154). -/
theorem mnat_convex_satisfies_gs (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) : MNatGS f := by sorry

end DiscreteConvex.MConvexFunctionsC
