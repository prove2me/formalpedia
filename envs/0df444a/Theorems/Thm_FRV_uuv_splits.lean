-- Prove2me | Theorems.Thm_FRV_uuv_splits
-- name    : FRV.uuv_splits
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:11:34.880608+00:00
-- url     : https://prove2.me/theorems/5d5ccb0f-4b27-45fe-94a0-b2611643b38a
-- title:
--   The unrestricted group splits over its pure subgroup (Proposition 4.5)
-- statement:
--   The universal unrestricted virtual braid group splits as the semidirect product of its pure subgroup with the symmetric group. The permutation epimorphism onto the symmetric group admits a group-theoretic section carrying each transposition to the class of the corresponding virtual generator, so the pure sequence of the unrestricted setting splits. This is Proposition 4.5 of the paper.
-- source:
--   O. Ocampo, C. Stylianakis, Forbidden relations in universal virtual braid groups, arXiv:2606.06095 (2026), Section 4 (Proposition 4.5).

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

namespace FRV

/-!  Milestone 6 (Proposition 4.5): the universal unrestricted virtual
braid group splits as the semidirect product of its pure subgroup with the
symmetric group. The permutation epimorphism onto the symmetric group
admits a group-theoretic section, carrying each transposition to the class
of the corresponding virtual generator. -/
theorem uuv_splits {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type*}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) (hn : 3 ≤ n) :
    ∃ sec : Equiv.Perm (Fin n) →* U, ∀ p : Equiv.Perm (Fin n), W.uuvPerm (sec p) = p := by sorry

end FRV
