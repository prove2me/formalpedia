-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexity_integrally_convex_iff_restriction
-- name    : DiscreteConvex.IntegralConvexity.integrally_convex_iff_restriction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:52:29.541498+00:00
-- url     : https://prove2.me/theorems/69c4c2f3-0761-498b-948f-bba5fdc41c45
-- title:
--   Proposition 3.19 -- integral convexity is pointwise-local
-- statement:
--   **Proposition 3.19** (p.94). A function $f : \mathbb Z^n \to \mathbb R \cup \{+\infty\}$ is integrally convex if and only if its restriction $f_{[a,b]}$ to every integer interval $[a,b]$ is integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94, Proposition 3.19.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94, Proposition 3.19

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexity_Restrict

namespace DiscreteConvex.IntegralConvexity

/-- Proposition 3.19 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.94). A function
`f : Zⁿ → R ∪ {+∞}` is integrally convex if and only if its restriction `f_{[a,b]}` to every
integer interval `[a,b]` is integrally convex. -/
theorem integrally_convex_iff_restriction {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) :
    IntegrallyConvex f ↔ ∀ a b : Fin n → ℤ, IntegrallyConvex (Restrict f a b) := by sorry

end DiscreteConvex.IntegralConvexity
