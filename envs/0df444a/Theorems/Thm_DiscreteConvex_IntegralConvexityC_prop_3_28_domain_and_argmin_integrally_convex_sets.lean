-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityC_prop_3_28_domain_and_argmin_integrally_convex_sets
-- name    : DiscreteConvex.IntegralConvexityC.prop_3_28_domain_and_argmin_integrally_convex_sets
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:14:47.389122+00:00
-- url     : https://prove2.me/theorems/5ce5f34d-647e-4217-9661-f6759c1dac4c
-- title:
--   Proposition 3.28 -- the domain and minimizer sets of an integrally convex function are integrally convex
-- statement:
--   For integrally convex $f$: $\operatorname{dom}_{\mathbb Z}f$ and every $\arg\min f[-p]$ are integrally convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Proposition 3.28.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Proposition 3.28

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.97, Proposition 3.28, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.28.** Let `f : Zⁿ → R∪{+∞}` be integrally convex. (1) `dom_Z f` is an
integrally convex set. (2) For each `p ∈ Rⁿ`, `arg min f[-p]` is an integrally convex set. -/
theorem prop_3_28_domain_and_argmin_integrally_convex_sets {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hf : IntegrallyConvex f) :
    IntegrallyConvexSet (DomZ f) ∧
      ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p) := by sorry

end DiscreteConvex.IntegralConvexityC
