-- Prove2me | Theorems.Thm_CannonFloydParry_isFinitelyPresented_F
-- name    : CannonFloydParry.isFinitelyPresented_F
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:47:41.598946+00:00
-- url     : https://prove2.me/theorems/f8b3c9b9-82b5-4019-95b8-ed521921c74f
-- title:
--   Thompson's group $F$ is finitely presented
-- statement:
--   Thompson's group $F$ is finitely presented in Mathlib's sense
--   (`Group.IsFinitelyPresented`): it is finitely generated and the kernel of some surjection from
--   a free group of finite rank onto it is the normal closure of finitely many elements. No specific
--   presentation is named in the statement.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3 (a consequence of Theorem 3.4; the source states the presentation, not this phrase)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Consequence of Theorem 3.4: Thompson's group `F` is finitely presented. -/
theorem isFinitelyPresented_F : Group.IsFinitelyPresented F := by
  sorry

end CannonFloydParry
