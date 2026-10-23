-- Prove2me | Theorems.Thm_FRV_theta_zeta_involutions
-- name    : FRV.theta_zeta_involutions
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:08:38.46069+00:00
-- url     : https://prove2.me/theorems/6a324de0-9c5b-4588-a23e-1b17568fcd64
-- title:
--   The automorphisms theta and zeta are commuting involutions (Theorem 2.1)
-- statement:
--   The automorphisms theta and zeta_1, ..., zeta_k of the universal virtual braid group are mutually commuting involutions. Each zeta_l fixes the virtual generators, sends the l-th sigma family to its conjugate by the adjacent virtual generator, and fixes the other sigma families; theta inverts every sigma generator and fixes the virtual generators. Each automorphism is its own inverse, theta commutes with every zeta_l, and the zeta_l commute pairwise. This is the involution part of Theorem 2.1 of the paper.
-- source:
--   O. Ocampo, C. Stylianakis, Forbidden relations in universal virtual braid groups, arXiv:2606.06095 (2026), Section 2 (Theorem 2.1, the involution statements).

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

namespace FRV

/-!  Milestone 1 (Theorem 2.1, involutions): the automorphisms theta and
zeta_1, ..., zeta_k of the universal virtual braid group are commuting
involutions. Each zeta_l fixes the virtual generators, sends the l-th
sigma family to its conjugate rho_i sigma_(i,l) rho_i, and fixes the other
families; theta inverts every sigma generator; the compositions are
mutually commuting involutions. -/
theorem theta_zeta_involutions {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type*}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) :
    IsInvolutive W.theta ∧
    (∀ l : Fin k, IsInvolutive (W.zeta l)) ∧
    (∀ l : Fin k, ∀ x : V, W.theta (W.zeta l x) = W.zeta l (W.theta x)) ∧
    (∀ l m : Fin k, ∀ x : V, W.zeta l (W.zeta m x) = W.zeta m (W.zeta l x)) := by sorry

end FRV
