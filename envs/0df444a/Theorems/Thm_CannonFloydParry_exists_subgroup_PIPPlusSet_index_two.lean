-- Prove2me | Theorems.Thm_CannonFloydParry_exists_subgroup_PIPPlusSet_index_two
-- name    : CannonFloydParry.exists_subgroup_PIPPlusSet_index_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:06:36.906233+00:00
-- url     : https://prove2.me/theorems/37e1982a-ecee-4266-9bcc-d42a5228b498
-- title:
--   p. 251 — PIP⁺(Δₙ) is a subgroup of index 2 in PIP(Δₙ) (n ≥ 1)
-- statement:
--   For $n \ge 1$, there are subgroups $H \ge K$ of the homeomorphism group of $\Delta_n$ whose elements are exactly the PIP homeomorphisms and exactly the orientation-preserving ones, and $K$ has index $2$ in $H$.
--
--   **Formalization Note.** Orientation-preserving is expressed through the pieces: on each simplex of some integral subdivision the map is $\rho \circ A$ with $\det A = 1$. The hypothesis $n \ge 1$ is not in the source; for $n = 0$, $\Delta_0$ is a point, both sets contain only the identity, and the index is $1$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 251, after Theorem 7.1

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem exists_subgroup_PIPPlusSet_index_two {n : ℕ} (hn : 1 ≤ n) :
    ∃ H K : Subgroup (Simplex n ≃ₜ Simplex n),
      (H : Set (Simplex n ≃ₜ Simplex n)) = PIPSet n ∧
      (K : Set (Simplex n ≃ₜ Simplex n)) = PIPPlusSet n ∧ K ≤ H ∧ (K.subgroupOf H).index = 2 := by
  sorry

end CannonFloydParry
