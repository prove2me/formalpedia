-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctions_m_optimality_criterion
-- name    : DiscreteConvex.MConvexFunctions.m_optimality_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:59:28.074221+00:00
-- url     : https://prove2.me/theorems/e748ee86-77fb-42c7-acb7-c6b28ccb5828
-- title:
--   Theorem 6.26 -- the M-optimality criterion
-- statement:
--   **Theorem 6.26** (p.148). (1) For an M-convex function $f$ and $x \in \operatorname{dom} f$, $f(x) \le f(y)$ for all $y \in \mathbb Z^V$ if and only if $f(x) \le f(x-\chi_u+\chi_v)$ for all $u,v \in V$. (2) For an M$^\natural$-convex function $f$ and $x \in \operatorname{dom} f$, global optimality is equivalent to the same exchange condition together with $f(x) \le f(x \pm \chi_v)$ for all $v \in V$.
--
--   This sharpens chunk 03's Theorem 3.21 (integral convexity's local-to-global principle, checked over the full $3^n-1$ sign-pattern neighborhood) to a finite neighbor set of size $O(n^2)$ — exactly the pairs $(u,v)$ — which is what makes M-convexity a useful refinement of plain integral convexity for algorithm design.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Theorem 6.26.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Theorem 6.26

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec

namespace DiscreteConvex.MConvexFunctions

/-- Theorem 6.26, the M-optimality criterion (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.148). (1) For an M-convex function `f` and `x ∈ dom f`, `f(x) ≤ f(y)` for all `y ∈ Zⱽ` iff
`f(x) ≤ f(x - χ_u + χ_v)` for all `u, v ∈ V`. (2) For an M♮-convex function `f` and
`x ∈ dom f`, `f(x) ≤ f(y)` for all `y ∈ Zⱽ` iff both `f(x) ≤ f(x - χ_u + χ_v)` for all
`u, v ∈ V` and `f(x) ≤ f(x ± χ_v)` for all `v ∈ V`. -/
theorem m_optimality_criterion {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, MExchangeAxiom f → ∀ x ∈ DomZ f,
      (∀ y, f x ≤ f y) ↔ (∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w))) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNaturalConvex f → ∀ x ∈ DomZ f,
      (∀ y, f x ≤ f y) ↔
        ((∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w)) ∧
          (∀ v : V, f x ≤ f (fun w => x w + CharVec v w) ∧
            f x ≤ f (fun w => x w - CharVec v w)))) := by sorry

end DiscreteConvex.MConvexFunctions
