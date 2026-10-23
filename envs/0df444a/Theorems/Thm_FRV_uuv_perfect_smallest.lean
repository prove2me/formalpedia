-- Prove2me | Theorems.Thm_FRV_uuv_perfect_smallest
-- name    : FRV.uuv_perfect_smallest
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:12:38.440517+00:00
-- url     : https://prove2.me/theorems/d66c6006-f3cf-4ddc-853e-fb40b378669d
-- title:
--   The commutator subgroup is perfect and S_n is the smallest non-Abelian finite quotient (Proposition 4.7 and Corollary 4.9)
-- statement:
--   For n at least five, the commutator subgroup of the universal unrestricted virtual braid group is perfect, and the symmetric group is its smallest non-Abelian finite quotient, realized through the permutation epimorphism; the same two conclusions hold for the multi-unrestricted braid group. The forbidden relations lie in the commutator subgroup of the universal virtual braid group, so the perfectness passes to the quotients. These are Proposition 4.7 and Corollary 4.9 of the paper, the main structural theorems of the mission.
-- source:
--   O. Ocampo, C. Stylianakis, Forbidden relations in universal virtual braid groups, arXiv:2606.06095 (2026), Section 4 (Proposition 4.7, with Corollary 4.9).

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

namespace FRV

/-!  The goal (Proposition 4.7 and Corollary 4.9): for n at least five,
the commutator subgroup of the universal unrestricted virtual braid group
is perfect, and the symmetric group S_n is its smallest non-Abelian finite
quotient; the same holds for the multi-unrestricted braid group M_kUB_n.
The forbidden relations lie in the commutator subgroup of the universal
virtual braid group, so the perfectness of the commutator subgroup passes
to the quotients, and the symmetric group is realized through the
permutation map. -/
theorem uuv_perfect_smallest {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type*}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) (hn : 5 ≤ n) :
    (Derived (↥(Derived U)) = ⊤ ∧ FiniteQuotientsAbelianBelow U (Nat.factorial n)) ∧
    (Derived (↥(Derived Mk)) = ⊤ ∧ FiniteQuotientsAbelianBelow Mk (Nat.factorial n)) ∧
    (∀ p : Equiv.Perm (Fin n), ∃ x : U, W.uuvPerm x = p) := by sorry

end FRV
