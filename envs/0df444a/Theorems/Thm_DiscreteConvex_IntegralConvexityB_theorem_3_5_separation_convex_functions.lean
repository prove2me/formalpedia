-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_5_separation_convex_functions
-- name    : DiscreteConvex.IntegralConvexityB.theorem_3_5_separation_convex_functions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:05:24.80486+00:00
-- url     : https://prove2.me/theorems/53977a18-99e6-43d4-b903-56f7602b8388
-- title:
--   Theorem 3.5 -- separation theorem for convex/concave functions
-- statement:
--   Under (a1) or (a2), $f\ge h$ implies an affine function separating $f$ and $h$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104, Theorem 3.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104, Theorem 3.5

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConcave
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE
import Definitions.Def_DiscreteConvex_IntegralConvexityB_RelInt
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConcave

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.104, Theorem 3.5, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- **Theorem 3.5** (Separation for convex functions). Let `f` be a proper convex function and
`h` a proper concave function, and assume (a1) or (a2). If `f(x) ≥ h(x)` for all `x`, there
exist `α* ∈ R` and `p* ∈ Rⁿ` such that `f(x) ≥ α* + ⟨p*,x⟩ ≥ h(x)` for all `x`. -/
theorem theorem_3_5_separation_convex_functions {V : Type*} [Fintype V] (f h : (V → ℝ) → EReal)
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (ha : (RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧ (DomE f ∩ DomE h).Nonempty))
    (hge : ∀ x : V → ℝ, f x ≥ h x) :
    ∃ (astar : ℝ) (pstar : V → ℝ), ∀ x : V → ℝ,
      f x ≥ (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ∧
        (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ≥ h x := by sorry

end DiscreteConvex.IntegralConvexityB
