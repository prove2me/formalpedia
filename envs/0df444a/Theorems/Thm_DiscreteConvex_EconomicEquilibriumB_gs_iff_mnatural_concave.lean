-- Prove2me | Theorems.Thm_DiscreteConvex_EconomicEquilibriumB_gs_iff_mnatural_concave
-- name    : DiscreteConvex.EconomicEquilibriumB.gs_iff_mnatural_concave
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T06:14:10.54387+00:00
-- url     : https://prove2.me/theorems/6db830e2-0a8a-4a14-b517-5771ebfb38fe
-- title:
--   Theorem 11.5 -- gs_iff_mnatural_concave
-- statement:
--   **Theorem 11.5** (p.331). For a concave-extensible function $U:\mathbb Z^K\to\mathbb R\cup\{-\infty\}$ with a bounded nonempty effective domain, $U$ is M$^
--   atural$-concave iff $U$ satisfies (−M$^
--   atural$-GS[Z]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, Theorem 11.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, Theorem 11.5

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsConcaveExtensible
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_NegGS

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Theorem 11.5 (p.331). For a concave-extensible function `U` with bounded nonempty effective
domain, `U` is M♮-concave iff `U` satisfies (−M♮-GS[Z]). -/
theorem gs_iff_mnatural_concave (U : (K → ℤ) → WithBot ℝ) (hconc : IsConcaveExtensible U)
    (hbdd : ∃ N : ℤ, ∀ x ∈ UDom U, ∀ k, |x k| ≤ N) (hne : (UDom U).Nonempty) :
    MNaturalConcave U ↔ NegGS U := by sorry

end DiscreteConvex.EconomicEquilibriumB
