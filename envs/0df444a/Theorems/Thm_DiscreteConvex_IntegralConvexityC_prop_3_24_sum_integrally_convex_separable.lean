-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityC_prop_3_24_sum_integrally_convex_separable
-- name    : DiscreteConvex.IntegralConvexityC.prop_3_24_sum_integrally_convex_separable
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:12:39.300562+00:00
-- url     : https://prove2.me/theorems/af453dca-504e-4bc6-b069-2770e6d6bc5b
-- title:
--   Proposition 3.24 -- sum of an integrally convex and a separable convex function
-- statement:
--   The sum of an integrally convex function and a separable convex function is integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.95, Proposition 3.24.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.95, Proposition 3.24

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_SeparableConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.95, Proposition 3.24, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.24.** The sum of an integrally convex function and a separable convex
function is an integrally convex function. -/
theorem prop_3_24_sum_integrally_convex_separable {n : ℕ} (f0 fsep : (Fin n → ℤ) → WithTop ℝ)
    (h0 : IntegrallyConvex f0) (hsep : SeparableConvex fsep) :
    IntegrallyConvex (fun x => f0 x + fsep x) := by sorry

end DiscreteConvex.IntegralConvexityC
