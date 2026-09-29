-- Prove2me | Theorems.Thm_CannonFloydParry_exists_represents
-- name    : CannonFloydParry.exists_represents
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:09:38.114647+00:00
-- url     : https://prove2.me/theorems/17a32b48-04ab-42da-b5ed-dcbd0ab384c4
-- title:
--   Every tree diagram represents an element of $F$
-- statement:
--   For every tree diagram — an ordered pair of trees with the same number of leaves —
--   there is an element of Thompson's group $F$ that represents it: it lies in $F$, is affine on
--   every interval of the partition cut out by the domain tree, and carries that partition's
--   breakpoints, in order, to those of the partition cut out by the range tree.
--
--   No uniqueness is claimed, and none holds: distinct tree diagrams can represent the same element,
--   which is exactly why reduced diagrams are introduced.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 221 (existence half of the correspondence with $F$)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem exists_represents (d : TreeDiagram) : ∃ f : UI ≃o UI, Represents d f := by
  sorry

end CannonFloydParry
