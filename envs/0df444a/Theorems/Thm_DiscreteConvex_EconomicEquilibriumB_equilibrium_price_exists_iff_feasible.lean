-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibriumB_equilibrium_price_exists_iff_feasible
-- name    : DiscreteConvex.EconomicEquilibriumB.equilibrium_price_exists_iff_feasible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T06:14:45.176058+00:00
-- url     : https://prove2.me/theorems/4722b93d-e412-4db6-9189-aa057dcd67b9
-- title:
--   Theorem 11.22 -- equilibrium_price_exists_iff_feasible
-- statement:
--   **Theorem 11.22** (p.344). There exists an equilibrium price vector (for the allocation $(x,y)$) iff the linear system (11.43)/(11.44) is feasible.
--
--   **Scope note.** The book's own trailing algorithmic remarks (that the smallest/largest equilibrium price vectors can be found by solving a shortest-path problem, and the resulting polynomial-time algorithm for checking equilibrium existence) are computational/complexity content and are omitted; the mathematical "iff feasibility" content is placed in full. See `HARD.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.344, Theorem 11.22.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.344, Theorem 11.22

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPriceSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPricePolyhedronE
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConvexC
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsOptimalAllocation

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Theorem 11.22 (p.344). There exists an equilibrium price vector (for the allocation `(x,y)`)
iff the linear system (11.44)/(11.43) is feasible.  Murota, *Discrete Convex Analysis*, SIAM 2003, §11.5 assumes the utilities
M♮-concave, the cost functions M♮-convex and `(x,y)` an optimal allocation of the associated
MSFP2, and its bounds are read in `EReal`: with one good, one consumer with `U(0) = U(1) = 0`,
`U(2) = 5` and `-∞` elsewhere and one producer with `C(0) = C(2) = 0`, `C(1) = 1`, the equilibrium
price set is empty while the bounds taken with `unbotD 0`/`untopD 0` give `{0}`. -/
theorem equilibrium_price_exists_iff_feasible {H L : Type*} [Fintype H] [Fintype L] [Nonempty H]
    [Nonempty L] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) (hU : ∀ h, MNaturalConcave (U h)) (hC : ∀ l, MNaturalConvexC (C l))
    (hopt : IsOptimalAllocation U C x y) :
    (EquilibriumPriceSet U C x y).Nonempty ↔ (EquilibriumPricePolyhedronE U C x y).Nonempty := by sorry

end DiscreteConvex.EconomicEquilibriumB
