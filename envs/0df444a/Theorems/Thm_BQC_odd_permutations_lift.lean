-- Prove2me | Theorems.Thm_BQC_odd_permutations_lift
-- name    : BQC.odd_permutations_lift
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:28:23.944821+00:00
-- url     : https://prove2.me/theorems/80e068e2-9756-4c3a-b34e-ba08e6f55f7c
-- title:
--   The odd-order elements of the permutation layer lift to the quotient (Corollary 4)
-- statement:
--   The torsion of the quotient of the Artin braid group by the commutator subgroup of its pure braid group is exactly the odd torsion of the symmetric group: every element of the permutation layer of odd exact order r is the projection of an element of the quotient of the same exact order r. The lift is constructed through the normal form of Section 3 of the source paper and the products of the elements of Proposition 21. This is the realization half of Corollary 4; together with the absence of even torsion of Theorem 2 it characterizes the torsion of the quotient.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Sections 1 and 4 (Corollary 4).

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor

namespace BQC

/-!  Milestone 4 (Corollary 4): every element of odd order of the permutation
layer lifts to an element of the same exact order in the braid quotient. The
torsion of the quotient is exactly the odd torsion of the symmetric group; the
lift is constructed through the normal form of Section 3 and the products of
the elements of Proposition 21. -/
theorem odd_permutations_lift {n : Nat} {Q S : Type*} [Group Q] [Group S] [Fintype S]
    (W : BraidQuotient n Q S) (hn : 3 ≤ n) (th : S) (r : Nat)
    (hr : ExactOrder r th) (hodd : Odd r) :
    ∃ b : Q, ExactOrder r b ∧ W.proj b = th := by sorry

end BQC
