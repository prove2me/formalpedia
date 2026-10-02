-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibriumB_swgs_iff_mnatural_concave
-- name    : DiscreteConvex.EconomicEquilibriumB.swgs_iff_mnatural_concave
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T06:14:30.703816+00:00
-- url     : https://prove2.me/theorems/b3bdd3b8-3907-4c52-a9b0-dc2957e1d731
-- title:
--   Theorem 11.6 -- swgs_iff_mnatural_concave
-- statement:
--   **Theorem 11.6** (p.331). For a concave-extensible function $U:\mathbb Z^K\to\mathbb R\cup\{-\infty\}$ with a nonempty effective domain, $U$ is M$^
--   atural$-concave iff $U$ satisfies (−M$^
--   atural$-SWGS[Z]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, Theorem 11.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, Theorem 11.6

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsConcaveExtensible
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_NegSWGS

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Theorem 11.6 (p.331). For a concave-extensible function `U` with nonempty effective domain,
`U` is M♮-concave iff `U` satisfies (−M♮-SWGS[Z]). -/
theorem swgs_iff_mnatural_concave (U : (K → ℤ) → WithBot ℝ) (hconc : IsConcaveExtensible U)
    (hne : (UDom U).Nonempty) :
    MNaturalConcave U ↔ NegSWGS U := by sorry

end DiscreteConvex.EconomicEquilibriumB
