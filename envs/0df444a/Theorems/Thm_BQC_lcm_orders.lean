-- Prove2me | Theorems.Thm_BQC_lcm_orders
-- name    : BQC.lcm_orders
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:29:42.103157+00:00
-- url     : https://prove2.me/theorems/39a76154-21e1-44a0-8943-90d1c9cfeb70
-- title:
--   The least common multiple orders are realized in the larger quotient (Theorem 3(b))
-- statement:
--   The braid quotient on m strings possesses elements of every odd order realized by the smaller quotient: given the injective inclusion homomorphism of the quotients of Theorem 3(a), an element of odd exact order r of the smaller permutation layer lifts through the inclusion to an element of the same exact order in the larger quotient, whose projection is the embedded element. Together with Proposition 21 this constructs the elements of the least common multiple orders of Theorem 3(b), with the prescribed cycle type.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Sections 1 and 4 (Theorem 3(b), with Proposition 21).

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor

namespace BQC

/-!  Milestone 7 (Theorem 3(b)): the braid quotient on m strings possesses
elements of every odd order realized by the smaller quotient. Given the
injective inclusion homomorphism of the quotients of milestone 6, an element
of odd exact order r of the smaller permutation layer lifts through the
inclusion to an element of the same exact order in the larger quotient, whose
permutation has the corresponding cycle type. Together with Proposition 21
this constructs elements of the least common multiple orders of Theorem 3. -/
theorem lcm_orders {n m : Nat} {Q1 S1 Q2 S2 : Type*} [Group Q1] [Group S1] [Fintype S1]
    [Group Q2] [Group S2] [Fintype S2]
    (W1 : BraidQuotient n Q1 S1) (W2 : BraidQuotient m Q2 S2)
    (iS : S1 →* S2) (hiS : ∀ x y : S1, iS x = iS y → x = y)
    (iQ : Q1 →* Q2) (hcomm : ∀ q : Q1, W2.proj (iQ q) = iS (W1.proj q))
    (hiQ : ∀ x y : Q1, iQ x = iQ y → x = y)
    (th : S1) (r : Nat) (hr : ExactOrder r th) (hodd : Odd r) :
    ∃ b : Q2, ExactOrder r b ∧ W2.proj b = iS th := by sorry

end BQC
