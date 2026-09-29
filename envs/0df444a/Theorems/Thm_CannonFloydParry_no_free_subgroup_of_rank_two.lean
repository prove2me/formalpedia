-- Prove2me | Theorems.Thm_CannonFloydParry_no_free_subgroup_of_rank_two
-- name    : CannonFloydParry.no_free_subgroup_of_rank_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:31:00.547632+00:00
-- url     : https://prove2.me/theorems/77f21c0b-146c-45b5-a718-6ee3ffa4de95
-- title:
--   $F$ contains no non-Abelian free group
-- statement:
--   Thompson's group $F$ contains no non-Abelian free group. Equivalently, and as stated
--   here, no ordered pair of elements of $F$ is a free basis: for any two elements $f$ and $g$ of
--   $F$, the homomorphism from the free group on two generators sending the generators to $f$ and
--   $g$ is not injective.
--
--   The two forms are equivalent because every non-Abelian free group contains a free group of rank
--   two. This is Brin and Squier's theorem, which they proved for the larger group of
--   orientation-preserving piecewise-linear homeomorphisms of the line having slope $1$ at both
--   ends.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Corollary 4.9, p. 232

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem no_free_subgroup_of_rank_two (f g : UI ≃o UI) (hf : f ∈ F) (hg : g ∈ F) :
    ¬ Function.Injective (FreeGroup.lift ![f, g]) := by
  sorry

end CannonFloydParry
