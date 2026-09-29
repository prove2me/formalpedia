-- Prove2me | Theorems.Thm_CannonFloydParry_exists_isPositiveV1_mul_of_mem_PiUnion
-- name    : CannonFloydParry.exists_isPositiveV1_mul_of_mem_PiUnion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:26:47.611948+00:00
-- url     : https://prove2.me/theorems/7d12be70-8a7c-4a77-b0a3-c3cadac912f0
-- title:
--   Lemma 6.7 — $\pi p = p'\pi'$
-- statement:
--   In $V_1$, if $p$ is positive and $\pi \in \Pi$, then $\pi p = p'\pi'$ for some positive $p'$ and some $\pi' \in \Pi$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 247, Lemma 6.7

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem exists_isPositiveV1_mul_of_mem_PiUnion {p π : V1} (hp : IsPositiveV1 p) (hπ : π ∈ PiUnion) :
    ∃ p' π', IsPositiveV1 p' ∧ π' ∈ PiUnion ∧ π * p = p' * π' := by
  sorry

end CannonFloydParry
