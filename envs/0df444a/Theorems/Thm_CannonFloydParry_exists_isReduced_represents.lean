-- Prove2me | Theorems.Thm_CannonFloydParry_exists_isReduced_represents
-- name    : CannonFloydParry.exists_isReduced_represents
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:10:08.870422+00:00
-- url     : https://prove2.me/theorems/8664f0c1-e229-4288-ae1a-abedf9deffd9
-- title:
--   Every element of $F$ has a reduced tree diagram
-- statement:
--   Every $f$ in Thompson's group $F$ is represented by some **reduced** tree diagram: one
--   in which no position carries a caret in both trees, so that there is no $k$ for which the $k$th
--   and $(k+1)$th leaves of the domain tree are siblings and the $k$th and $(k+1)$th leaves of the
--   range tree are siblings as well.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 221 (existence of the reduced diagram)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem exists_isReduced_represents {f : UI ≃o UI} (hf : f ∈ F) :
    ∃ d : TreeDiagram, IsReduced d ∧ Represents d f := by
  sorry

end CannonFloydParry
