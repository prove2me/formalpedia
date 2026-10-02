-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_submodular_iff_assoc_fn_lnat_convex
-- name    : DiscreteConvex.LConvexFunctionsB.submodular_iff_assoc_fn_lnat_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:24:39.120135+00:00
-- url     : https://prove2.me/theorems/923f26ae-51ae-4e01-acda-4cf66354a1e1
-- title:
--   Proposition 7.4 -- submodular_iff_assoc_fn_lnat_convex
-- statement:
--   **Proposition 7.4** (p.179). Let $\rho:2^V\to\mathbb R\cup\{+\infty\}$ be a set function with $\operatorname{dom}\rho\ne\emptyset$ and $g$ its associated function (Eq. (7.5)). Then $\rho$ is submodular iff $g$ is L$^\natural$-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.179, Proposition 7.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.179, Proposition 7.4

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_Submodular
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_AssocFn

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.4 (p.179). A set function `ρ` is submodular iff its associated function `g`
is L♮-convex. -/
theorem submodular_iff_assoc_fn_lnat_convex (rho : Finset V → WithTop ℝ)
    (hdom : ∃ X, rho X ≠ ⊤) :
    Submodular rho ↔ LNaturalConvex (AssocFn rho) := by sorry

end DiscreteConvex.LConvexFunctionsB
