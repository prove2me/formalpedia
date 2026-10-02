-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctions_l_optimality_criterion
-- name    : DiscreteConvex.LConvexFunctions.l_optimality_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:15:29.458191+00:00
-- url     : https://prove2.me/theorems/a1392d66-9818-4f4d-a533-8ee83b5d295d
-- title:
--   Theorem 7.14 -- the L-optimality criterion
-- statement:
--   **Theorem 7.14** (p.185). (1) For an L-convex function $g$ and $p \in \operatorname{dom} g$, $g(p) \le g(q)$ for all $q \in \mathbb Z^V$ if and only if both $g(p) \le g(p+\chi_Y)$ for all $Y \subseteq V$ and $g(p) = g(p+\mathbf 1)$. (2) For an L$^\natural$-convex function $g$ and $p \in \operatorname{dom} g$, global optimality is equivalent to $g(p) \le g(p \pm \chi_Y)$ for all $Y \subseteq V$. Part (1)'s extra periodicity condition $g(p)=g(p+\mathbf 1)$ is a genuine, load-bearing hypothesis of the plain L-convex case, not a technical footnote — it is exactly what is *not* needed in the L$^\natural$-convex case, since that normalization is built into the class differently.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185, Theorem 7.14.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185, Theorem 7.14

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctions_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctions_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctions_IndicatorVec

namespace DiscreteConvex.LConvexFunctions

/-- Theorem 7.14, the L-optimality criterion (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.185). (1) For an L-convex function `g` and `p ∈ dom g`, `g(p) ≤ g(q)` for all `q ∈ Zⱽ` iff
both `g(p) ≤ g(p + χ_Y)` for all `Y ⊆ V` and `g(p) = g(p + 1)`. (2) For an L♮-convex function
`g` and `p ∈ dom g`, `g(p) ≤ g(q)` for all `q ∈ Zⱽ` iff `g(p) ≤ g(p ± χ_Y)` for all `Y ⊆ V`. -/
theorem l_optimality_criterion {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ g : (V → ℤ) → WithTop ℝ, SBF g → TRF g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔
        ((∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v)) ∧
          g p = g (fun v => p v + 1))) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNaturalConvex g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔
        (∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v) ∧
          g p ≤ g (fun v => p v - IndicatorVec Y v))) := by sorry

end DiscreteConvex.LConvexFunctions
