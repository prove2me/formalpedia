-- Prove2me | Theorems.Thm_Chou_isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isSolvable
-- name    : Chou.isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isSolvable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T14:07:57.214467+00:00
-- url     : https://prove2.me/theorems/924a0e51-e518-4965-acac-85c206c7b4d3
-- title:
--   Rosenblatt's theorem: a finitely generated solvable group is almost nilpotent or contains a free subsemigroup on two generators
-- statement:
--   Let $G$ be a finitely generated solvable group. Then either $G$ has a nilpotent subgroup
--   of finite index, or $G$ contains a free subsemigroup on two generators, that is, a pair of elements
--   on which the evaluation map from the free monoid on two letters is injective.
--
--   Chou states this on p. 401 as Rosenblatt's sharpening of the Milnor–Wolf theorem, and observes why
--   it is sharper: a group containing a free subsemigroup on two generators has exponential growth, so
--   the second alternative here is more informative than "has exponential growth". It is what Chou uses
--   to upgrade Theorem 3.2 to Theorem 3.2′.
--
--   "Almost nilpotent" is Mathlib's `Group.IsVirtuallyNilpotent`, a nilpotent subgroup of finite index;
--   the free subsemigroup condition is the published growth bundle's predicate.
-- source:
--   Rosenblatt, J. M., Invariant measures and growth conditions, Transactions of the American Mathematical Society 193 (1974) 33–53, https://doi.org/10.1090/S0002-9947-1974-0342955-9, the theorem Chou states on p. 401 of Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608: “In [21], Rosenblatt modified the proofs of Milnor and Wolf to obtain the following: If G is a finitely generated solvable group then G is either almost nilpotent or it contains a free subsemigroup on two generators.”

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- Rosenblatt's theorem, as Chou states it (p. 401, external): "In [21], Rosenblatt modified the
proofs of Milnor and Wolf to obtain the following: If `G` is a finitely generated solvable group
then `G` is either almost nilpotent or it contains a free subsemigroup on two generators."
Reference [21] is J. M. Rosenblatt, *Invariant measures and growth conditions*, Trans. Amer. Math.
Soc. 193 (1974) 33–53.

"Almost nilpotent" is Mathlib's `Group.IsVirtuallyNilpotent`, a nilpotent subgroup of finite index;
`HasFreeSubsemigroupOfRankTwo` is the published growth bundle's predicate. Chou notes that this is
stronger than the Milnor–Wolf theorem, since a group with a free subsemigroup on two generators has
exponential growth. -/
theorem isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isSolvable {G : Type*} [Group G]
    [Group.FG G] [Group.IsSolvable G] :
    Group.IsVirtuallyNilpotent G ∨ HasFreeSubsemigroupOfRankTwo G := by
  sorry

end Chou
