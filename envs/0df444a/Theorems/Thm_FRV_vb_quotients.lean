-- Prove2me | Theorems.Thm_FRV_vb_quotients
-- name    : FRV.vb_quotients
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:11:15.131559+00:00
-- url     : https://prove2.me/theorems/e1aa8747-c593-47dc-ad8e-df7e106d86ba
-- title:
--   The one-forbidden quotients of the multi-virtual braid group are isomorphic (Corollary 3.2 and Remark 3.3)
-- statement:
--   The one-forbidden quotients of the multi-virtual braid group associated with the two forbidden relations are isomorphic, by the same theta construction transported along the multi-virtual projection. For k equal to one the multi-virtual braid group is the virtual braid group, so the quotients by the normal closures of the two forbidden relations are abstractly isomorphic; since the first quotient is the welded braid group, so is the second, although the second forbidden relation does not hold there in the original generators. This is Corollary 3.2 with Remark 3.3 of the paper.
-- source:
--   O. Ocampo, C. Stylianakis, Forbidden relations in universal virtual braid groups, arXiv:2606.06095 (2026), Section 3 (Corollary 3.2, with Remark 3.3).

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

namespace FRV

/-!  Milestone 5 (Corollary 3.2 and Remark 3.3): the one-forbidden
quotients of the multi-virtual braid group M_kVB_n associated with the two
forbidden relations are isomorphic. For k equal to one, M_1VB_n is the
virtual braid group VB_n, so the quotient of VB_n by the normal closure of
either forbidden relation is abstractly isomorphic to the welded braid
group WB_n, although the second forbidden relation does not hold in WB_n
in the original generators. -/
theorem vb_quotients {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type*}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) (hn : 3 ≤ n) :
    ∃ e : QM1 ≃* QM2, ∀ x : V, e (W.pm1 x) = W.pm2 (W.theta x) := by sorry

end FRV
