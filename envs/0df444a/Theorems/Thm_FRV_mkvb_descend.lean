-- Prove2me | Theorems.Thm_FRV_mkvb_descend
-- name    : FRV.mkvb_descend
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:10:06.950958+00:00
-- url     : https://prove2.me/theorems/92f41d77-914d-4e25-8849-1d7fda4f9eea
-- title:
--   The automorphisms descend to the multi-virtual braid group (Corollary 2.3)
-- statement:
--   The automorphisms theta and zeta_k descend to commuting involutive automorphisms of the multi-virtual braid group: the multi-virtual relations are invariant under the automorphisms, so each is compatible with the quotient projection. Neither the descended theta, nor the descended zeta_k, nor their composition is an inner automorphism, so their classes generate a subgroup of the outer automorphism group isomorphic to Z_2 x Z_2. This is Corollary 2.3 of the paper.
-- source:
--   O. Ocampo, C. Stylianakis, Forbidden relations in universal virtual braid groups, arXiv:2606.06095 (2026), Section 2 (Corollary 2.3).

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

namespace FRV

/-!  Milestone 3 (Corollary 2.3): the automorphisms theta and zeta_k
descend to commuting involutive automorphisms of the multi-virtual braid
group M_kVB_n, and their classes generate a subgroup of the outer
automorphism group isomorphic to Z_2 x Z_2: the descended automorphisms
are involutions, compatible with the quotient projection, and no
nontrivial one is inner. -/
theorem mkvb_descend {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type*}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) (hn : 3 ≤ n) :
    ∃ (phiTheta : Mk ≃* Mk) (phiZetaK : Mk ≃* Mk),
      IsInvolutive phiTheta ∧ IsInvolutive phiZetaK ∧
      (∀ x : V, phiTheta (W.pm x) = W.pm (W.theta x)) ∧
      (∀ x : V, phiZetaK (W.pm x) = W.pm (W.zeta ⟨k - 1, by have := W.hk; omega⟩ x)) ∧
      (¬ ∃ g : Mk, ∀ y : Mk, phiTheta y = g * y * g⁻¹) ∧
      (¬ ∃ g : Mk, ∀ y : Mk, phiZetaK y = g * y * g⁻¹) ∧
      (¬ ∃ g : Mk, ∀ y : Mk, phiTheta (phiZetaK y) = g * y * g⁻¹) := by sorry

end FRV
