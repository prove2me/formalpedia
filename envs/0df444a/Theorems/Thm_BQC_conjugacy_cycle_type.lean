-- Prove2me | Theorems.Thm_BQC_conjugacy_cycle_type
-- name    : BQC.conjugacy_cycle_type
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:28:50.239352+00:00
-- url     : https://prove2.me/theorems/742e5a31-a428-472a-bd69-b7d31127ec71
-- title:
--   Conjugacy of the odd-order elements is read off from the permutation layer (Theorem 5)
-- statement:
--   Two elements of the braid quotient of the same odd order k at least three are conjugate in the quotient if and only if their images are conjugate in the permutation layer. Conjugacy of the finite-order elements of odd order at least three is thus determined by the cycle types of the permutations; likewise two cyclic subgroups of the same odd order are conjugate exactly when their images are conjugate in the permutation layer. This is Theorem 5 of the source paper, the main result of its Section 6.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Section 6 (Theorem 5).

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor

namespace BQC

/-!  Milestone 5 (Theorem 5): two elements of the braid quotient of the same
odd order at least three are conjugate in the quotient if and only if their
images are conjugate in the permutation layer. Conjugacy of elements of odd
order is read off from the permutation layer; likewise two cyclic subgroups of
the same odd order are conjugate exactly when their images are. -/
theorem conjugacy_cycle_type {n : Nat} {Q S : Type*} [Group Q] [Group S] [Fintype S]
    (W : BraidQuotient n Q S) (k : Nat) (hk : 3 ≤ k) (hodd : Odd k)
    (x y : Q) (hx : ExactOrder k x) (hy : ExactOrder k y) :
    (∃ c : Q, c * x * c⁻¹ = y) ↔
      (∃ s : S, s * W.proj x * s⁻¹ = W.proj y) := by sorry

end BQC
