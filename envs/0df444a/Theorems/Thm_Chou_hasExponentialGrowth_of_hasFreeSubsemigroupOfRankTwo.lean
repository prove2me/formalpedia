-- Prove2me | Theorems.Thm_Chou_hasExponentialGrowth_of_hasFreeSubsemigroupOfRankTwo
-- name    : Chou.hasExponentialGrowth_of_hasFreeSubsemigroupOfRankTwo
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:56:38.506738+00:00
-- url     : https://prove2.me/theorems/5a709ba1-b83c-4b13-962c-6f5c955ebe2b
-- title:
--   A free subsemigroup on two generators forces exponential growth
-- statement:
--   If a finitely generated group contains a free subsemigroup on two generators, it has
--   exponential growth.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 401 (after Theorem 3.2)

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- p. 401: a finitely generated group containing a free subsemigroup on two generators has
exponential growth. -/
theorem hasExponentialGrowth_of_hasFreeSubsemigroupOfRankTwo {G : Type*} [Group G] [Group.FG G]
    (h : HasFreeSubsemigroupOfRankTwo G) : HasExponentialGrowth G := by
  sorry

end Chou
