-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_lnat_convex_iff_submodular_integrally_convex
-- name    : DiscreteConvex.LConvexFunctionsC.lnat_convex_iff_submodular_integrally_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:52:29.77737+00:00
-- url     : https://prove2.me/theorems/d156341e-3124-49cb-a780-bb3a719a917b
-- title:
--   Theorem 7.21 -- lnat_convex_iff_submodular_integrally_convex
-- statement:
--   **Theorem 7.21** (p.189). For a function $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom} g\ne\emptyset$, $g$ is L$^\natural$-convex iff $g$ is submodular integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.189, Theorem 7.21.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.189, Theorem 7.21

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsIntegrallyConvexFunction

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.21 (p.189). `g` is L♮-convex iff `g` is submodular integrally convex. -/
theorem lnat_convex_iff_submodular_integrally_convex (g : (V → ℤ) → WithTop ℝ)
    (hdom : (DomZ g).Nonempty) :
    LNaturalConvex g ↔ (SBF g ∧ IsIntegrallyConvexFunction g) := by sorry

end DiscreteConvex.LConvexFunctionsC
