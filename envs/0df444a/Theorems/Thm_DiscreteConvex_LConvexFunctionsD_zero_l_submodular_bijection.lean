-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_zero_l_submodular_bijection
-- name    : DiscreteConvex.LConvexFunctionsD.zero_l_submodular_bijection
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:08:28.737898+00:00
-- url     : https://prove2.me/theorems/14e9c25e-b5e5-4216-a93a-46eced6a8245
-- title:
--   Theorem 7.40 -- zero_l_submodular_bijection
-- statement:
--   **Theorem 7.40** (p.195). For $0L=0L[\mathbb R\to\mathbb R]$ and $S=S[\mathbb R]$, the maps $\Phi:g\mapsto\rho_g$ (Eq. (7.35)) and $\Psi:\rho\mapsto\hat\rho$ (Eq. (7.36)) are inverse to each other, a one-to-one correspondence between $0L$ and $S$. The same holds for $0L=0L[\mathbb Z\to\mathbb Z]$ and $S=S[\mathbb Z]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.195, Theorem 7.40.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.195, Theorem 7.40

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LovaszExtension
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRho
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRhoZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.40 (p.195). The one-to-one correspondence between positively homogeneous L-convex
functions and submodular set functions. -/
theorem zero_l_submodular_bijection :
    (∀ g : (V → ℝ) → WithTop ℝ, ZeroLR g → LovaszExtension (InducedRho g) = g) ∧
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → InducedRho (LovaszExtension rho) = rho) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, ZeroLZZ g →
      (fun p : V → ℤ => LovaszExtension (InducedRhoZ g) (fun v => (p v : ℝ))) = g) ∧
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → IsIntegerValued rho →
      InducedRhoZ (fun p : V → ℤ => LovaszExtension rho (fun v => (p v : ℝ))) = rho) := by sorry

end DiscreteConvex.LConvexFunctionsD
