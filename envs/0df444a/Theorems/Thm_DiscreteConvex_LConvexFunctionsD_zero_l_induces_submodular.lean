-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_zero_l_induces_submodular
-- name    : DiscreteConvex.LConvexFunctionsD.zero_l_induces_submodular
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:08:18.763412+00:00
-- url     : https://prove2.me/theorems/6ac2aed9-c4db-42f7-acf5-4117428ef735
-- title:
--   Proposition 7.38 -- zero_l_induces_submodular
-- statement:
--   **Proposition 7.38** (p.194). (1) For $g\in 0L[\mathbb R\to\mathbb R]$, $\rho_g\in S[\mathbb R]$. (2) For $g\in 0L[\mathbb Z\to\mathbb Z]$, $\rho_g\in S[\mathbb Z]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Proposition 7.38.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Proposition 7.38

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRho
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRhoZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.38 (p.194). A positively homogeneous L-(natural-)convex function induces a
submodular set function. -/
theorem zero_l_induces_submodular :
    (∀ g : (V → ℝ) → WithTop ℝ, ZeroLR g → SubmodularSetFunction (InducedRho g)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, ZeroLZZ g →
      SubmodularSetFunction (InducedRhoZ g) ∧ IsIntegerValued (InducedRhoZ g)) := by sorry

end DiscreteConvex.LConvexFunctionsD
