-- Prove2me | Theorems.Thm_Chou_isVirtuallyNilpotent_of_extension_of_not_hasFreeSubsemigroupOfRankTwo
-- name    : Chou.isVirtuallyNilpotent_of_extension_of_not_hasFreeSubsemigroupOfRankTwo
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:01:04.818263+00:00
-- url     : https://prove2.me/theorems/1b6365ad-68d0-47bd-9282-e6b16600e69c
-- title:
--   Rosenblatt's form of Lemma 3.1 (external)
-- statement:
--   Let $A$ be a normal subgroup of the finitely generated group $B$ such that $A$ and $B/A$ each
--   have a nilpotent subgroup of finite index, and suppose $B$ contains no free subsemigroup on two
--   generators. Then $B$ has a nilpotent subgroup of finite index.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 401 (Rosenblatt [21], Lemmas 4.8 and 4.9, as applied by Chou)

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- Rosenblatt's form of Lemma 3.1 (p. 401, external): if `A` is normal in the finitely generated
group `B`, `A` and `B ⧸ A` are almost nilpotent and `B` contains no free subsemigroup on two
generators, then `B` is almost nilpotent. -/
theorem isVirtuallyNilpotent_of_extension_of_not_hasFreeSubsemigroupOfRankTwo {B : Type*} [Group B] [Group.FG B]
    (A : Subgroup B) [A.Normal] (hA : Group.IsVirtuallyNilpotent A)
    (hC : Group.IsVirtuallyNilpotent (B ⧸ A)) (hfree : ¬ HasFreeSubsemigroupOfRankTwo B) :
    Group.IsVirtuallyNilpotent B := by
  sorry

end Chou
