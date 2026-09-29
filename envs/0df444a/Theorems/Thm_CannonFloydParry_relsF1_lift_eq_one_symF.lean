-- Prove2me | Theorems.Thm_CannonFloydParry_relsF1_lift_eq_one_symF
-- name    : CannonFloydParry.relsF1_lift_eq_one_symF
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:44:41.204978+00:00
-- url     : https://prove2.me/theorems/b2de3057-1981-405c-b5d5-39f3bcf8e109
-- title:
--   The relators of $F_1$ hold for the functions $A$, $B$ (Example 1.2)
-- statement:
--   Under the assignment $A \mapsto A$, $B \mapsto B$ of the formal symbols to the two
--   generating homeomorphisms of Thompson's group, extended to the free group on $\{A, B\}$, each
--   of the two relators $[AB^{-1}, A^{-1}BA]$ and $[AB^{-1}, A^{-2}BA^{2}]$ is sent to the identity map of
--   $[0,1]$. Equivalently, $A \mapsto A$, $B \mapsto B$ extends to a homomorphism from $F_1$ into the
--   group of order isomorphisms of $[0,1]$ (its image lies in $F$, but that is not part of this
--   statement).
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, p. 226 (proof of Theorem 3.4, first paragraph), citing Example 1.2, p. 217

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Theorem 3.4, first step (Example 1.2): the two defining relators of `F₁` hold for the
functions `A`, `B` of Thompson's group, so `A ↦ mapA`, `B ↦ mapB` extends to a homomorphism
from `F₁` into the interval maps. -/
theorem relsF1_lift_eq_one_symF : ∀ r ∈ relsF1, FreeGroup.lift symF r = 1 := by
  sorry

end CannonFloydParry
