-- Prove2me | Theorems.Thm_FRV_outer_independent
-- name    : FRV.outer_independent
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:09:25.92629+00:00
-- url     : https://prove2.me/theorems/4643aea9-e8b4-484c-b55a-c9e40739b579
-- title:
--   The subproducts of theta and the zeta are outer (Theorem 2.1)
-- statement:
--   For n at least three, every nontrivial subproduct of the automorphisms of Theorem 2.1 is not an inner automorphism of the universal virtual braid group: the product of the zeta over a nonempty list of indices, optionally composed with theta, never acts as conjugation by a single element. The proof projects to the unrestricted quotient and uses the action on the abelianization together with the non-innerness technique of Makri. The classes therefore generate a subgroup of the outer automorphism group isomorphic to the elementary Abelian 2-group of rank k+1. This is the outer part of Theorem 2.1 of the paper.
-- source:
--   O. Ocampo, C. Stylianakis, Forbidden relations in universal virtual braid groups, arXiv:2606.06095 (2026), Section 2 (Theorem 2.1).

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

namespace FRV

/-!  Milestone 2 (Theorem 2.1): the classes of theta, zeta_1, ..., zeta_k
generate a subgroup isomorphic to (Z_2)^(k+1) in the outer automorphism
group of the universal virtual braid group: every nontrivial subproduct -
zeta over a nonempty list of indices, optionally composed with theta - is
not inner. The proof projects to the unrestricted virtual braid group and
uses the action on the abelianization together with the Makri proposition
on non-innerness. -/
theorem outer_independent {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type*}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) (hn : 3 ≤ n) :
    ∀ (L : List (Fin k)) (eps : Bool), (L ≠ [] ∨ eps = true) →
      ¬ ∃ g : V, ∀ x : V, zetaApplied W L eps x = g * x * g⁻¹ := by sorry

end FRV
