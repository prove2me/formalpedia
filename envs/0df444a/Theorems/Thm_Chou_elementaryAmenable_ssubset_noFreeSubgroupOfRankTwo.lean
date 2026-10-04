-- Prove2me | Theorems.Thm_Chou_elementaryAmenable_ssubset_noFreeSubgroupOfRankTwo
-- name    : Chou.elementaryAmenable_ssubset_noFreeSubgroupOfRankTwo
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T23:05:13.374633+00:00
-- url     : https://prove2.me/theorems/999c94c6-e95a-4209-81d3-07be51ac2c46
-- title:
--   Chou, Theorem 2.3 — EG is a proper subclass of NF
-- statement:
--   Every elementary amenable group (`Chou.ElementaryAmenable`) contains no free subgroup of rank two (`Chou.NoFreeSubgroupOfRankTwo`), and some group contains no free subgroup of rank two without being elementary amenable. Together: the class $EG$ of elementary amenable groups is properly contained in the class $NF$ of groups with no free subgroup on two generators. The inclusion is stated for groups in every universe; the witness of properness is a group in `Type`.
--
--   Chou writes on p. 398: “**Theorem 2.3.** *Every periodic group in $EG$ is locally finite. Therefore $EG \subsetneq NF$.*” The mission's milestones carry the first sentence and, of the second, only that $NF \setminus EG$ is nonempty ([`Chou.exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable`](https://prove2.me/theorems/aad542f4-5cb9-422d-8d67-f4a7389970fc)); this statement is the second sentence as printed, inclusion included. Chou takes the inclusion from p. 396 (“$NF$ … contains $AG$”) and the fact that elementary amenable groups are amenable; the proof composes the published [`Garrido.isAmenable_of_elementaryAmenable`](https://prove2.me/theorems/71cf52ae-8f55-4330-90ac-86de0259e1e9) and [`Garrido.noFreeSubgroupOfRankTwo_of_isAmenable`](https://prove2.me/theorems/185138b1-296a-4ea7-8a61-299815357e7b).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 398, Theorem 2.3

import Mathlib
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes

universe u

namespace Chou

theorem elementaryAmenable_ssubset_noFreeSubgroupOfRankTwo :
    (∀ (G : Type u) [Group G], ElementaryAmenable G → NoFreeSubgroupOfRankTwo G) ∧
      ∃ (G : Type) (_ : Group G), NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G := by
  sorry

end Chou
