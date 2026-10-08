-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibriumB_equilibrium_price_set_is_lnat_polyhedron
-- name    : DiscreteConvex.EconomicEquilibriumB.equilibrium_price_set_is_lnat_polyhedron
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T06:14:21.67767+00:00
-- url     : https://prove2.me/theorems/c11099d3-d16b-492d-99ba-95d3d2d10241
-- title:
--   Theorem 11.21 -- equilibrium_price_set_is_lnat_polyhedron
-- statement:
--   **Theorem 11.21** (p.343). GOAL. The set $P^*$ of all equilibrium price vectors for a given allocation $(x,y)$ is an L$^
--   atural$-convex polyhedron, described explicitly by the inequality system (11.43): $\max\{0,\ell(j)\}\le p(j)\le u(j)$ for $j\in K$ and $p(j)-p(i)\le u(i,j)$ for $i
--   e j$.
--
--   Chosen as goal: this is the sharpest structural result of chapter 11's computation section, upgrading the qualitative L$^
--   atural$-convex-polyhedron fact (Theorem 11.16, mission `14-economic-equilibrium`) to a concrete, linear-programming-checkable description, and is the fact Theorem 11.22 (also placed) builds on directly.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Theorem 11.21.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Theorem 11.21

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsLNaturalConvexPolyhedron
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPriceSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPricePolyhedronE
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConvexC
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsOptimalAllocation

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Theorem 11.21 (p.343). GOAL. The set `P*` of all equilibrium price vectors for a given
allocation `(x,y)` is an L♮-convex polyhedron, described explicitly by the inequality system
(11.43).  Murota, *Discrete Convex Analysis*, SIAM 2003, §11.5 assumes the utilities
M♮-concave, the cost functions M♮-convex and `(x,y)` an optimal allocation of the associated
MSFP2, and its bounds `ℓ(j)`, `u(j)`, `u(i,j)` are read in `EReal`: with one good, one consumer
with `U(0) = U(1) = 0`, `U(2) = 5` and `-∞` elsewhere and one producer with `C` the indicator of
`0`, the equilibrium price set is `{p ≥ 5/2}` while the bounds taken with `unbotD 0`/`untopD 0`
give `{0}`. -/
theorem equilibrium_price_set_is_lnat_polyhedron {H L : Type*} [Fintype H] [Fintype L]
    [Nonempty H] [Nonempty L] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (x : H → (K → ℤ)) (y : L → (K → ℤ))
    (hU : ∀ h, MNaturalConcave (U h)) (hC : ∀ l, MNaturalConvexC (C l))
    (hopt : IsOptimalAllocation U C x y) :
    IsLNaturalConvexPolyhedron (EquilibriumPriceSet U C x y) ∧
    EquilibriumPriceSet U C x y = EquilibriumPricePolyhedronE U C x y := by sorry

end DiscreteConvex.EconomicEquilibriumB
