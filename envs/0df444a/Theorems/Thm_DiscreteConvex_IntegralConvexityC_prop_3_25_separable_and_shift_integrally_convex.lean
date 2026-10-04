-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityC_prop_3_25_separable_and_shift_integrally_convex
-- name    : DiscreteConvex.IntegralConvexityC.prop_3_25_separable_and_shift_integrally_convex
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:12:40.664664+00:00
-- url     : https://prove2.me/theorems/a85f6316-9d97-41de-b806-3236b99c42c3
-- title:
--   Proposition 3.25 -- separable convex functions are integrally convex; shifts preserve it
-- statement:
--   A separable convex function is integrally convex, and $f[-p]$ is integrally convex whenever $f$ is.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.96, Proposition 3.25.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.96, Proposition 3.25

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_SeparableConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.96, Proposition 3.25, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.25.** (1) A separable convex function is integrally convex.
(2) `f[-p]` is integrally convex for integrally convex `f` and vector `p ∈ Rⁿ`. -/
theorem prop_3_25_separable_and_shift_integrally_convex {n : ℕ} :
    (∀ f : (Fin n → ℤ) → WithTop ℝ, SeparableConvex f → IntegrallyConvex f) ∧
      (∀ f : (Fin n → ℤ) → WithTop ℝ, IntegrallyConvex f → ∀ p : Fin n → ℝ,
        IntegrallyConvex (fun x => f x - ((∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ))) := by sorry

end DiscreteConvex.IntegralConvexityC
