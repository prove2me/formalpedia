-- Prove2me | Theorems.Thm_Chou_exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable
-- name    : Chou.exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:55:36.388673+00:00
-- url     : https://prove2.me/theorems/aad542f4-5cb9-422d-8d67-f4a7389970fc
-- title:
--   Theorem 2.3: $NF \setminus EG$ is nonempty
-- statement:
--   There is a group which has no free subgroup on two generators and is not elementary
--   amenable.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Theorem 2.3, second statement, p. 398

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Theorem 2.3, second statement: `NF \ EG` is nonempty — there is a group with no free subgroup
on two generators which is not elementary amenable. -/
theorem exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable :
    ∃ (G : Type) (_ : Group G), NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G := by
  sorry

end Chou
