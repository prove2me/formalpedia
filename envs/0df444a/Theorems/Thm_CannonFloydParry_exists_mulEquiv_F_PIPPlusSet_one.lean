-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_F_PIPPlusSet_one
-- name    : CannonFloydParry.exists_mulEquiv_F_PIPPlusSet_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:10:42.746419+00:00
-- url     : https://prove2.me/theorems/f35ea75c-a385-4eac-b30d-214dd4e8538d
-- title:
--   Theorem 7.2 — F ≅ PIP⁺(Δ₁)
-- statement:
--   The orientation-preserving PIP homeomorphisms of $\Delta_1$ form a subgroup of the homeomorphism group of $\Delta_1$, and Thompson's group $F$ is isomorphic to it.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 253, Theorem 7.2

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem exists_mulEquiv_F_PIPPlusSet_one :
    ∃ H : Subgroup (Simplex 1 ≃ₜ Simplex 1),
      (H : Set (Simplex 1 ≃ₜ Simplex 1)) = PIPPlusSet 1 ∧ Nonempty (F ≃* H) := by
  sorry

end CannonFloydParry
