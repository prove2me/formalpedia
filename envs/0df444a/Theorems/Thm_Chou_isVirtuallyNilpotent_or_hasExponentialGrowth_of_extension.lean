-- Prove2me | Theorems.Thm_Chou_isVirtuallyNilpotent_or_hasExponentialGrowth_of_extension
-- name    : Chou.isVirtuallyNilpotent_or_hasExponentialGrowth_of_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:59:58.801849+00:00
-- url     : https://prove2.me/theorems/cffa1bd3-c405-444b-bd5d-524dad155954
-- title:
--   Lemma 3.1: extensions of almost nilpotent by almost nilpotent groups
-- statement:
--   Let $A$ be a normal subgroup of the finitely generated group $B$ such that $A$ and $B/A$ each
--   have a nilpotent subgroup of finite index. Then $B$ has a nilpotent subgroup of finite index, or
--   $B$ has exponential growth.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Lemma 3.1, pp. 399–400

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- Lemma 3.1: if `A` is normal in the finitely generated group `B` with `A` and `B ⧸ A` almost
nilpotent, then `B` is almost nilpotent or has exponential growth. -/
theorem isVirtuallyNilpotent_or_hasExponentialGrowth_of_extension {B : Type*} [Group B] [Group.FG B] (A : Subgroup B) [A.Normal]
    (hA : Group.IsVirtuallyNilpotent A) (hC : Group.IsVirtuallyNilpotent (B ⧸ A)) :
    Group.IsVirtuallyNilpotent B ∨ HasExponentialGrowth B := by
  sorry

end Chou
