-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityC_theorem_3_29_integrally_convex_iff_argmin_sets
-- name    : DiscreteConvex.IntegralConvexityC.theorem_3_29_integrally_convex_iff_argmin_sets
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:14:59.245167+00:00
-- url     : https://prove2.me/theorems/de521353-d346-48ee-8023-a27d0cf205cd
-- title:
--   Theorem 3.29 -- integral convexity is equivalent to integral convexity of every minimizer set (GOAL)
-- statement:
--   For $f$ with nonempty bounded effective domain: $f$ is integrally convex iff $\arg\min f[-p]$ is an integrally convex set for every $p$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Theorem 3.29.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Theorem 3.29

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IsBoundedZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.97, Theorem 3.29 — the goal of this mission —
in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Theorem 3.29** (goal). Suppose `f : Zⁿ → R∪{+∞}` has a nonempty bounded effective domain.
Then `f` is integrally convex iff `arg min f[-p]` is an integrally convex set for every
`p ∈ Rⁿ`. -/
theorem theorem_3_29_integrally_convex_iff_argmin_sets {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hne : (DomZ f).Nonempty) (hbdd : IsBoundedZ (DomZ f)) :
    IntegrallyConvex f ↔ ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p) := by sorry

end DiscreteConvex.IntegralConvexityC
