-- Prove2me | Theorems.Thm_BQC_product_inclusion
-- name    : BQC.product_inclusion
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:29:14.6207+00:00
-- url     : https://prove2.me/theorems/a9ec738b-beed-47a7-ae14-3221fa7ca28f
-- title:
--   The inclusion of the Artin braid groups induces an injective homomorphism of the quotients (Theorem 3(a))
-- statement:
--   If the braid quotient worlds of n and m strings are given with n at most m, and the permutation layer of the smaller embeds into the permutation layer of the larger, then there is a homomorphism of the quotients lifting that embedding: it commutes with the projections and is injective. The proof studies the normal form of Section 3 of the source paper for the image of an element of the product of the smaller quotients. This is Theorem 3(a), through which the elements of the least common multiple orders of Theorem 3(b) are realized.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Sections 1 and 4 (Theorem 3(a)).

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor

namespace BQC

/-!  Milestone 6 (Theorem 3(a)): the inclusion of the Artin braid groups
induces an injective homomorphism of the quotients. If the braid quotient
worlds of n and m strings are given with n at most m, and the permutation
layer of the smaller embeds into the permutation layer of the larger, then
there is a lift of that embedding to an injective homomorphism of the braid
quotients compatible with the projections. The proof studies the normal form
of Section 3 for the image of an element. -/
theorem product_inclusion {n m : Nat} {Q1 S1 Q2 S2 : Type*} [Group Q1] [Group S1] [Fintype S1]
    [Group Q2] [Group S2] [Fintype S2]
    (W1 : BraidQuotient n Q1 S1) (W2 : BraidQuotient m Q2 S2) (hnm : n ≤ m)
    (iS : S1 →* S2) (hiS : ∀ x y : S1, iS x = iS y → x = y) :
    ∃ iQ : Q1 →* Q2,
      (∀ q : Q1, W2.proj (iQ q) = iS (W1.proj q)) ∧
      (∀ x y : Q1, iQ x = iQ y → x = y) := by sorry

end BQC
