-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_submodular_local_criterion_open_balls
-- name    : DiscreteConvex.LConvexFunctionsC.submodular_local_criterion_open_balls
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:35:07.024695+00:00
-- url     : https://prove2.me/theorems/51c5fc53-b0b5-4dbb-b246-03ccbf543da6
-- title:
--   Proposition 7.23 -- submodular_local_criterion_open_balls
-- statement:
--   **Proposition 7.23** (p.190). Let $g:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ have closed effective domain. Then $g$ is submodular (SBF[R]) if, for each $p_0\in\operatorname{dom}_{\mathbb R} g$, there is $\varepsilon=\varepsilon(p_0)>0$ such that the submodularity inequality holds for all $p,q$ with $\|p-p_0\|_\infty\le\varepsilon$ and $\|q-p_0\|_\infty\le\varepsilon$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, Proposition 7.23.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, Proposition 7.23

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.23 (p.190). A sufficient local (open-ball) criterion for submodularity on a
closed domain. -/
theorem submodular_local_criterion_open_balls (g : (V → ℝ) → WithTop ℝ) (hclosed : IsClosed (DomR g))
    (hlocal : ∀ p0 ∈ DomR g, ∃ eps : ℝ, 0 < eps ∧ ∀ p q : V → ℝ,
      (∀ v, |p v - p0 v| ≤ eps) → (∀ v, |q v - p0 v| ≤ eps) →
      g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)) :
    SBFR g := by sorry

end DiscreteConvex.LConvexFunctionsC
