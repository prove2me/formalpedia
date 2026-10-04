-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_mnat_convex_supermodular
-- name    : DiscreteConvex.MConvexFunctionsB.mnat_convex_supermodular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:11:48.391377+00:00
-- url     : https://prove2.me/theorems/4b2cd40e-1083-48a9-9a34-9be8ad16eaea
-- title:
--   Theorem 6.19 -- mnat_convex_supermodular
-- statement:
--   **Theorem 6.19** (p.145), Eq. (6.48). An M$^\natural$-convex function $f$ is supermodular: $f(x)+f(y) \le f(x\vee y)+f(x\wedge y)$ for all $x,y \in \mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.145, Theorem 6.19, Eq. (6.48).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.145, Theorem 6.19

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.145, Theorem 6.19, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Theorem 6.19 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.145). See the item's
`natural_language_statement` for the full statement. -/
theorem mnat_convex_supermodular {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    ∀ x y : V → ℤ, f x + f y ≤ f (fun v => max (x v) (y v)) + f (fun v => min (x v) (y v)) := by sorry

end DiscreteConvex.MConvexFunctionsB
