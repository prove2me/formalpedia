-- Prove2me | Theorems.Thm_Chou_fg_of_isVirtuallyPolycyclic_quotient_of_not_hasFreeSubsemigroupOfRankTwo
-- name    : Chou.fg_of_isVirtuallyPolycyclic_quotient_of_not_hasFreeSubsemigroupOfRankTwo
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T12:44:58.080505+00:00
-- url     : https://prove2.me/theorems/9211bf44-08ed-4c79-bdb9-a8fca7a8a553
-- title:
--   Rosenblatt's Lemmas 4.8 and 4.9 in the form Chou uses them: with no free subsemigroup on two generators, a normal subgroup with virtually polycyclic quotient is finitely generated
-- statement:
--   Let $G$ be a finitely generated group with no free subsemigroup on two generators, and
--   let $N$ be a normal subgroup such that the quotient $G/N$ has a polycyclic subgroup of finite
--   index. Then $N$ is finitely generated.
--
--   This is the free-subsemigroup twin of the exponentially bounded statement, and the same correction
--   applies to it. Rosenblatt's Lemma 4.9 concludes that every element of the normal subgroup is a
--   product of conjugates of finitely many elements, which is normal generation; the passage to finite
--   generation needs the quotient's normal form, which a finite presentation does not supply. Chou
--   applies the pair to an almost nilpotent quotient.
--
--   Being virtually polycyclic is written out as the existence of a finite-index subgroup of $G/N$
--   satisfying the published definition of a polycyclic group.
-- source:
--   Rosenblatt, J. M., Invariant measures and growth conditions, Transactions of the American Mathematical Society 193 (1974) 33–53, https://doi.org/10.1090/S0002-9947-1974-0342955-9, Lemma 4.8 (p. 42) and Lemma 4.9 (p. 43), with the abelian hypothesis removed and stated for the virtually polycyclic quotient the assembly requires, as applied in Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 401, proof of Theorem 3.2′: “we may apply Lemmas 4.8 and 4.9 in [21] together with the understanding that A doesn't have to be abelian there”

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Chou

/-- Rosenblatt's Lemmas 4.8 and 4.9 (Trans. Amer. Math. Soc. 193 (1974), pp. 42–43) in the form
Chou's proof of Theorem 3.2′ uses them (p. 401, "with the understanding that `A` doesn't have to be
abelian there"): in a finitely generated group with no free subsemigroup on two generators, a
normal subgroup whose quotient is virtually polycyclic is finitely generated.

This is the free-subsemigroup twin of `Chou.fg_of_isVirtuallyPolycyclic_quotient`, and the same
remark applies: the passage from normal generation to finite generation is Milnor's Lemma 3, which
is stated for a polycyclic quotient and whose proof uses the polycyclic normal form, so a finitely
presented quotient is not enough. Chou applies the result to an almost nilpotent quotient.
"Virtually polycyclic" is written out as a finite-index subgroup satisfying the published
`MilnorWolf.IsPolycyclic`. -/
theorem fg_of_isVirtuallyPolycyclic_quotient_of_not_hasFreeSubsemigroupOfRankTwo {G : Type*}
    [Group G] [Group.FG G] (hfree : ¬ HasFreeSubsemigroupOfRankTwo G) (N : Subgroup G) [N.Normal]
    (hq : ∃ H : Subgroup (G ⧸ N), H.FiniteIndex ∧ MilnorWolf.IsPolycyclic H) :
    Group.FG N := by
  sorry

end Chou
