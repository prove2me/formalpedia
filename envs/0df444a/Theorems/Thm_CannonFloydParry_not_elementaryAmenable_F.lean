-- Prove2me | Theorems.Thm_CannonFloydParry_not_elementaryAmenable_F
-- name    : CannonFloydParry.not_elementaryAmenable_F
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T12:07:07.837064+00:00
-- url     : https://prove2.me/theorems/4f2f2764-a60c-4662-9ab1-1d347eab9a71
-- title:
--   Theorem 4.10: $F$ is not elementary amenable
-- statement:
--   Thompson's group $F$ does not belong to the class of elementary amenable groups, as defined
--   in the bundle `Chou_ElementaryAmenable`: the smallest class containing all finite
--   and all abelian groups and closed under isomorphism, subgroups, quotients, extensions and
--   directed unions. The class is taken within the universe of sets that contains $F$ itself (so
--   the groups and index sets appearing in a derivation are all sets of that size); no derivation
--   of that kind places $F$ in the class.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, Theorem 4.10, p. 233; the class is Chou's, Illinois J. Math. 24 (1980), p. 396.

import Definitions.Def_CannonFloydParry
import Definitions.Def_Chou_ElementaryAmenable
import Mathlib

namespace CannonFloydParry

/-- Theorem 4.10.  Thompson's group `F` is not elementary amenable. -/
theorem not_elementaryAmenable_F : ¬ Chou.ElementaryAmenable F := by
  sorry

end CannonFloydParry
