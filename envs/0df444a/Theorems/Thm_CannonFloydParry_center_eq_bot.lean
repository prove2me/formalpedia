-- Prove2me | Theorems.Thm_CannonFloydParry_center_eq_bot
-- name    : CannonFloydParry.center_eq_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:29:36.055983+00:00
-- url     : https://prove2.me/theorems/e59df514-409a-4dcb-8519-8c2aae592cbe
-- title:
--   The center of $F$ is trivial
-- statement:
--   The center of Thompson's group $F$ is trivial: the only element of $F$ that commutes with
--   every element of $F$ is the identity.
--
--   Cannon-Floyd-Parry establish this in the first paragraph of the proof of Theorem 4.3, arguing
--   from the fixed-point set of the generator $B$ and from Lemma 4.2.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, inside the proof of Theorem 4.3, p. 229

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem center_eq_bot : Subgroup.center F = ⊥ := by
  sorry

end CannonFloydParry
