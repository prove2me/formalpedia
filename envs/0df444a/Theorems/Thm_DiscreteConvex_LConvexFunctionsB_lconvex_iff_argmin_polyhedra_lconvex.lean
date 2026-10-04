-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_lconvex_iff_argmin_polyhedra_lconvex
-- name    : DiscreteConvex.LConvexFunctionsB.lconvex_iff_argmin_polyhedra_lconvex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:25:24.460439+00:00
-- url     : https://prove2.me/theorems/3e0c7a18-c752-423e-a267-9563f26aba79
-- title:
--   Theorem 7.17 -- lconvex_iff_argmin_polyhedra_lconvex
-- statement:
--   **Theorem 7.17** (p.186). GOAL. Let $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ have a bounded nonempty effective domain. (1) $g$ is L-convex iff $\arg\min g[-x]$ is an L-convex set for each $x\in\mathbb R^V$. (2) $g$ is L$^\natural$-convex iff $\arg\min g[-x]$ is an L$^\natural$-convex set for each $x\in\mathbb R^V$.
--
--   The direct L-side mirror of mission `23-ch06c-mconvexfunctions`'s Theorem 6.43: it characterizes L-convexity entirely in terms of the polyhedral structure of weighted minimizer sets, showing L-convex functions are exactly those obtained by consistently piecing together L-convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, Theorem 7.17.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, Theorem 7.17

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ArgMin
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNatConvexSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LinearWeight

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.17 (p.186). GOAL. For `g` with bounded nonempty effective domain, `g` is L-convex
(resp. L♮-convex) iff `arg min g[-x]` is an L-convex (resp. L♮-convex) set for every `x ∈ Rⱽ`. -/
theorem lconvex_iff_argmin_polyhedra_lconvex (g : (V → ℤ) → WithTop ℝ)
    (hne : (DomZ g).Nonempty) (hbdd : ∃ M : ℤ, ∀ p ∈ DomZ g, ∀ v, |p v| ≤ M) :
    ((SBF g ∧ TRF g) ↔ ∀ x : V → ℝ, LConvexSet (ArgMin (LinearWeight g (fun v => - x v)))) ∧
    (LNaturalConvex g ↔
      ∀ x : V → ℝ, LNatConvexSet (ArgMin (LinearWeight g (fun v => - x v)))) := by sorry

end DiscreteConvex.LConvexFunctionsB
