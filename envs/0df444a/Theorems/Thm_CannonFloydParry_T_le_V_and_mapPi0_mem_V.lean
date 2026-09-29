-- Prove2me | Theorems.Thm_CannonFloydParry_T_le_V_and_mapPi0_mem_V
-- name    : CannonFloydParry.T_le_V_and_mapPi0_mem_V
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:21:34.476989+00:00
-- url     : https://prove2.me/theorems/28933571-d23b-46e3-bfeb-b4e18886356f
-- title:
--   p. 240 — $T \le V$ and $\pi_0 \in V$
-- statement:
--   Thompson's group $T$ is a subgroup of $V$, and the map $\pi_0$ of p. 240 lies in $V$.
--
--   **Formalization Note.** The source uses both facts without comment: it defines $\pi_0$ as a map of the circle and speaks of "elements $X_n$ and $C_n$ of $V$" and of "the subgroup $F$ of $V$".
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 240, the definition of π₀

import Mathlib
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem T_le_V_and_mapPi0_mem_V : T ≤ V ∧ mapPi0 ∈ V := by
  sorry

end CannonFloydParry
