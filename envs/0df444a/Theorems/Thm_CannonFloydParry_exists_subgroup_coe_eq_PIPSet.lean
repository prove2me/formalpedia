-- Prove2me | Theorems.Thm_CannonFloydParry_exists_subgroup_coe_eq_PIPSet
-- name    : CannonFloydParry.exists_subgroup_coe_eq_PIPSet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:06:14.554811+00:00
-- url     : https://prove2.me/theorems/dcb168e2-f76c-4404-b269-00c7d0589f34
-- title:
--   p. 249 — PIP(Δₙ) is a group
-- statement:
--   For every $n$, the PIP homeomorphisms of $\Delta_n$ form a group under composition: some subgroup of the homeomorphism group of $\Delta_n$ has exactly them as its elements.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 249, PIP homeomorphisms

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem exists_subgroup_coe_eq_PIPSet (n : ℕ) :
    ∃ H : Subgroup (Simplex n ≃ₜ Simplex n), (H : Set (Simplex n ≃ₜ Simplex n)) = PIPSet n := by
  sorry

end CannonFloydParry
