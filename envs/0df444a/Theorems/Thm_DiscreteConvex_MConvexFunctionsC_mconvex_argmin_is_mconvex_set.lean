-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mconvex_argmin_is_mconvex_set
-- name    : DiscreteConvex.MConvexFunctionsC.mconvex_argmin_is_mconvex_set
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:30:41.423134+00:00
-- url     : https://prove2.me/theorems/c17febef-338c-4db1-b86d-8a99e48b1d6c
-- title:
--   Proposition 6.29 -- mconvex_argmin_is_mconvex_set
-- statement:
--   **Proposition 6.29** (p.150). For an M-convex function $f \in M[\mathbb Z \to \mathbb R]$, $\arg\min f$ is an M-convex set if it is not empty.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.150, Proposition 6.29.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.150, Proposition 6.29

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.29 (p.150). -/
theorem mconvex_argmin_is_mconvex_set (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hne : (ArgMinOn f).Nonempty) : ExchangeAxiomB (ArgMinOn f) := by sorry

end DiscreteConvex.MConvexFunctionsC
