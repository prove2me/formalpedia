-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_sbf_nat_r_iff_polyhedral_lnat_convex
-- name    : DiscreteConvex.LConvexFunctionsC.sbf_nat_r_iff_polyhedral_lnat_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:38:57.061626+00:00
-- url     : https://prove2.me/theorems/2ae9ce4e-2a4a-4367-9621-b48de7e1f347
-- title:
--   Theorem 7.28 -- sbf_nat_r_iff_polyhedral_lnat_convex
-- statement:
--   **Theorem 7.28** (p.192). For a polyhedral convex function $g:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom}_{\mathbb R} g\ne\emptyset$, (SBF$^\natural$[R]) is equivalent to polyhedral L$^\natural$-convexity.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, Theorem 7.28.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, Theorem 7.28

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFNatR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.28 (p.192). For a polyhedral convex function, (SBF♮[R]) is equivalent to polyhedral
L♮-convexity. -/
theorem sbf_nat_r_iff_polyhedral_lnat_convex (g : (V → ℝ) → WithTop ℝ) (hdom : (DomR g).Nonempty) :
    SBFNatR g ↔ LNaturalConvexR g := by sorry

end DiscreteConvex.LConvexFunctionsC
