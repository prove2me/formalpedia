-- Prove2me | Theorems.Thm_CannonFloydParry_bijOn_dyadic
-- name    : CannonFloydParry.bijOn_dyadic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:25:29.239805+00:00
-- url     : https://prove2.me/theorems/d415d25a-738d-475d-bfec-efd7f7934ac6
-- title:
--   $F$ permutes the dyadic rationals
-- statement:
--   Let $f$ be an element of Thompson's group $F$. Then $f$ restricts to a bijection of the
--   set of dyadic rational numbers lying in $[0,1]$ onto itself: it carries dyadic points to dyadic
--   points, it is injective there, and every dyadic point of $[0,1]$ is the image of one.
--
--   Cannon-Floyd-Parry record this immediately after defining $F$; it is the step from which they
--   deduce that $F$ is closed under composition.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 1, p. 217, the sentence 'f maps the set of dyadic rational numbers bijectively to itself'

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem bijOn_dyadic {f : UI ≃o UI} (hf : f ∈ F) :
    Set.BijOn f {z : UI | IsDyadic (z : ℝ)} {z : UI | IsDyadic (z : ℝ)} := by
  sorry

end CannonFloydParry
