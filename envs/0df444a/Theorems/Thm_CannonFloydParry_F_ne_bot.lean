-- Prove2me | Theorems.Thm_CannonFloydParry_F_ne_bot
-- name    : CannonFloydParry.F_ne_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:24:12.132954+00:00
-- url     : https://prove2.me/theorems/18c5a068-b7b7-44d2-adea-b552c584264a
-- title:
--   $F$ is not the trivial group
-- statement:
--   Thompson's group $F$ is not the trivial subgroup: it contains an element other than the
--   identity.
--
--   Cannon-Floyd-Parry's Example 1.1 exhibits two such elements explicitly, and the map they call
--   $A$ — which sends $x$ to $x/2$ on $[0,1/2]$, to $x - 1/4$ on $[1/2,3/4]$ and to $2x - 1$ on
--   $[3/4,1]$ — already witnesses this, since it moves the point $1/2$ to $1/4$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 1, Example 1.1, p. 217 (the functions A and B)

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem F_ne_bot : F ≠ ⊥ := by
  sorry

end CannonFloydParry
