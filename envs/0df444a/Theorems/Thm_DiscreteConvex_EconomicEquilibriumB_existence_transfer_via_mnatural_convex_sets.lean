-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibriumB_existence_transfer_via_mnatural_convex_sets
-- name    : DiscreteConvex.EconomicEquilibriumB.existence_transfer_via_mnatural_convex_sets
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T06:24:34.540839+00:00
-- url     : https://prove2.me/theorems/42e97fcc-77f9-439f-a580-6429d5cd157a
-- title:
--   Theorem 11.15 -- existence_transfer_via_mnatural_convex_sets
-- statement:
--   **Theorem 11.15** (p.338). Suppose that, for each $p\in\mathbb R^K_+$, demand sets $D_h(p)$ ($h\in H$) and supply sets $S_l(p)$ ($l\in L$) are M$^
--   atural$-convex if they are not empty. If the derived continuous economy has an equilibrium for a total initial endowment $x^\circ\in\mathbb Z^K_+$, there exists an equilibrium of indivisible commodities for $x^\circ$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.338, Theorem 11.15.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.338, Theorem 11.15

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SupplySet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsEquilibrium
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsMNaturalConvexSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsContEquilibrium

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Theorem 11.15 (p.339). If demand and supply sets are M♮-convex whenever nonempty, and the
derived continuous economy has an equilibrium for `x° ∈ Zᴷ₊`, then an equilibrium of indivisible
commodities exists for `x°`. -/
theorem existence_transfer_via_mnatural_convex_sets {H L : Type*} [Fintype H] [Fintype L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (hD : ∀ p : K → ℝ, (∀ k, 0 ≤ p k) → ∀ h, (DemandSet (U h) p).Nonempty →
      IsMNaturalConvexSet (DemandSet (U h) p))
    (hS : ∀ p : K → ℝ, (∀ k, 0 ≤ p k) → ∀ l, (SupplySet (C l) p).Nonempty →
      IsMNaturalConvexSet (SupplySet (C l) p))
    (x0 : K → ℤ) (hx0 : ∀ k, 0 ≤ x0 k) (xc : H → (K → ℝ)) (yc : L → (K → ℝ)) (pc : K → ℝ)
    (hcont : IsContEquilibrium U C x0 xc yc pc) :
    ∃ (x : H → (K → ℤ)) (y : L → (K → ℤ)) (p : K → ℝ), IsEquilibrium U C x0 x y p := by sorry

end DiscreteConvex.EconomicEquilibriumB
