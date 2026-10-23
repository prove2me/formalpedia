-- Prove2me | Theorems.Thm_FRV_quotients_isomorphic
-- name    : FRV.quotients_isomorphic
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:10:41.559223+00:00
-- url     : https://prove2.me/theorems/c4a1a6fc-85f7-42df-aa19-c39ddfd3d0dd
-- title:
--   The two one-forbidden quotients are isomorphic (Theorem 3.1)
-- statement:
--   The two one-forbidden quotients of the universal virtual braid group are isomorphic. The automorphism theta inverts every sigma generator and fixes the virtual generators, so it carries the normal closure of the first forbidden family onto the normal closure of the second, and descends to an isomorphism between the two quotients, carrying the class of an element in the first quotient to the class of its theta-image in the second. This is Theorem 3.1 of the paper, which resolves the convention ambiguity between the two forbidden relations.
-- source:
--   O. Ocampo, C. Stylianakis, Forbidden relations in universal virtual braid groups, arXiv:2606.06095 (2026), Section 3 (Theorem 3.1).

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

namespace FRV

/-!  Milestone 4 (Theorem 3.1): the two one-forbidden quotients of the
universal virtual braid group are isomorphic. The automorphism theta
inverts the sigma generators and fixes the virtual generators, so it
carries the normal closure of the first family of forbidden relations onto
the normal closure of the second, and descends to an isomorphism between
the two one-forbidden quotients. -/
theorem quotients_isomorphic {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type*}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) (hn : 3 ≤ n) :
    ∃ e : Q1 ≃* Q2, ∀ x : V, e (W.p1 x) = W.p2 (W.theta x) := by sorry

end FRV
