-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_lovasz_extension_is_zero_l
-- name    : DiscreteConvex.LConvexFunctionsD.lovasz_extension_is_zero_l
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:08:44.062483+00:00
-- url     : https://prove2.me/theorems/6cb980f2-54cc-4414-a4ae-24af3b56fa94
-- title:
--   Proposition 7.39 -- lovasz_extension_is_zero_l
-- statement:
--   **Proposition 7.39** (p.195). (1) For $\rho\in S[\mathbb R]$, $\hat\rho\in 0L[\mathbb R\to\mathbb R]$. (2) For $\rho\in S[\mathbb Z]$, $\hat\rho_{\mathbb Z}\in 0L[\mathbb Z\to\mathbb Z]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.195, Proposition 7.39.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.195, Proposition 7.39

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LovaszExtension

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.39 (p.195). The Lovász extension of a submodular set function is positively
homogeneous L-convex. -/
theorem lovasz_extension_is_zero_l :
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → ZeroLR (LovaszExtension rho)) ∧
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → IsIntegerValued rho →
      ZeroLZZ (fun p : V → ℤ => LovaszExtension rho (fun v => (p v : ℝ)))) := by sorry

end DiscreteConvex.LConvexFunctionsD
