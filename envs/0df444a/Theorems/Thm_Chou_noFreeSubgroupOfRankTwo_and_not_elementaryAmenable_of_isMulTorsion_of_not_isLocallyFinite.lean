-- Prove2me | Theorems.Thm_Chou_noFreeSubgroupOfRankTwo_and_not_elementaryAmenable_of_isMulTorsion_of_not_isLocallyFinite
-- name    : Chou.noFreeSubgroupOfRankTwo_and_not_elementaryAmenable_of_isMulTorsion_of_not_isLocallyFinite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:55:06.311754+00:00
-- url     : https://prove2.me/theorems/a4bfb541-c5ea-4772-a46b-b9aff130426d
-- title:
--   Theorem 2.3, step: a non-locally finite periodic group lies in $NF \setminus EG$
-- statement:
--   If every element of $G$ has finite order and $G$ is not locally finite (some finitely
--   generated subgroup of $G$ is infinite), then no homomorphism from the free group on two generators
--   into $G$ is injective, and $G$ is not elementary amenable.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Theorem 2.3, proof, p. 398

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Theorem 2.3, the step on p. 398: a periodic group which is not locally finite has no free
subgroup on two generators and is not elementary amenable, that is, it lies in `NF \ EG`. -/
theorem noFreeSubgroupOfRankTwo_and_not_elementaryAmenable_of_isMulTorsion_of_not_isLocallyFinite {G : Type*} [Group G]
    (ht : IsMulTorsion G) (hnl : ¬ IsLocallyFinite G) :
    NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G := by
  sorry

end Chou
