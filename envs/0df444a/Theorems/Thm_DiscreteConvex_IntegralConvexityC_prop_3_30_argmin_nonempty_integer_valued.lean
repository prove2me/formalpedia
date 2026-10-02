-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityC_prop_3_30_argmin_nonempty_integer_valued
-- name    : DiscreteConvex.IntegralConvexityC.prop_3_30_argmin_nonempty_integer_valued
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:13:14.754566+00:00
-- url     : https://prove2.me/theorems/0f01a81c-d069-417d-8b5c-67b3c8a6d27d
-- title:
--   Proposition 3.30 -- nonempty minimizer set for integer-valued integrally convex functions
-- statement:
--   For integer-valued integrally convex $f$: $\arg\min f[-p]\ne\emptyset$ whenever $\inf f[-p]>-\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Proposition 3.30.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Proposition 3.30

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_InfPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_CastZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Proposition 3.30, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.30.** For an integer-valued integrally convex function
`f : Zⁿ → Z∪{+∞}` and `p ∈ Rⁿ`, `arg min f[-p] ≠ ∅` if `inf f[-p] > -∞`. -/
theorem prop_3_30_argmin_nonempty_integer_valued {n : ℕ} (f : (Fin n → ℤ) → WithTop ℤ)
    (hic : IntegrallyConvex (CastZR f)) (p : Fin n → ℝ)
    (hinf : InfPerturbed (CastZR f) p > ⊥) :
    (ArgMinPerturbed (CastZR f) p).Nonempty := by sorry

end DiscreteConvex.IntegralConvexityC
