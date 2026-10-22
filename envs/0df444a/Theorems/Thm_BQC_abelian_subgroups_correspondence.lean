-- Prove2me | Theorems.Thm_BQC_abelian_subgroups_correspondence
-- name    : BQC.abelian_subgroups_correspondence
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:30:09.217377+00:00
-- url     : https://prove2.me/theorems/074d8737-c57a-4636-b281-e49bb48c566c
-- title:
--   The finite Abelian subgroups of the quotient correspond to the odd Abelian subgroups of the permutation layer (Theorem 6)
-- statement:
--   There is a one-to-one correspondence between the isomorphism classes of the finite Abelian subgroups of the braid quotient and the isomorphism classes of the Abelian subgroups of the permutation layer of odd order. Every finite Abelian group of odd order embedded in the permutation layer is realized by a subgroup of the quotient - the lift of the embedding of Corollary 4 extended from the cyclic to the Abelian groups, following the invariant of Hoffman cited as [11] in the source paper - and every finite Abelian subgroup of the quotient has odd order, so by Lemma 9 it embeds isomorphically into the permutation layer. This is Theorem 6 of the source paper, the goal of the mission.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Section 6 (Theorem 6).

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor

namespace BQC

/-!  The goal (Theorem 6): there is a one-to-one correspondence between the
isomorphism classes of the finite Abelian subgroups of the braid quotient and
the isomorphism classes of the Abelian subgroups of the permutation layer of
odd order. Every finite Abelian group of odd order embedded in the
permutation layer is realized by a subgroup of the quotient - the lift of the
embedding of Corollary 4 extended to Abelian subgroups - and every finite
Abelian subgroup of the quotient has odd order, so by Lemma 9 it embeds
isomorphically into the permutation layer. -/
theorem abelian_subgroups_correspondence {n : Nat} {Q S : Type*} [Group Q] [Group S] [Fintype S]
    (W : BraidQuotient n Q S) (hn : 3 ≤ n) :
    (∀ (H : Type) [Group H] [Fintype H] [CommGroup H] (i : H →* S)
        (hi : ∀ x y : H, i x = i y → x = y) (hodd : Odd (Fintype.card H)), LiftsOver W i) ∧
    (∀ (H : Type) [Group H] [Fintype H] [CommGroup H] (f : H →* Q)
        (hf : ∀ x y : H, f x = f y → x = y), Odd (Fintype.card H)) := by sorry

end BQC
