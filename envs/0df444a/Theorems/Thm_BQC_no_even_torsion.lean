-- Prove2me | Theorems.Thm_BQC_no_even_torsion
-- name    : BQC.no_even_torsion
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T00:27:50.391378+00:00
-- url     : https://prove2.me/theorems/abb6a2e7-18ab-4f8f-bb07-e26a9afefd2c
-- title:
--   The braid quotient has no elements of even order (Theorem 2)
-- statement:
--   The quotient of the Artin braid group on n strings by the commutator subgroup of its pure braid group has no finite-order elements of even order: every element of the quotient of finite order has an odd positive power equal to the identity. The proof analyses the action of the quotient on the standard basis of the abelianization of the pure braid group: an element of even order would restrict to an action whose orbit structure contradicts the rigidity of the orbits of that action. This is Theorem 2 of the source paper, the upper bound of the torsion characterization of Corollary 4.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Sections 1 and 4 (Theorem 2).

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor

namespace BQC

/-!  Milestone 3 (Theorem 2): the quotient of the Artin braid group by the
commutator subgroup of its pure braid group has no elements of even order.
Every element of the quotient of finite order has an odd order. The proof
analyses the action of the quotient on the standard basis of the
abelianization of the pure braid group: an element of even order would
restrict to a double-cover-like action whose orbit parity contradicts the
structure of the action on the basis elements. -/
theorem no_even_torsion {n : Nat} {Q S : Type*} [Group Q] [Group S] [Fintype S]
    (W : BraidQuotient n Q S) (hn : 3 ≤ n) : NoEvenTorsion Q := by sorry

end BQC
