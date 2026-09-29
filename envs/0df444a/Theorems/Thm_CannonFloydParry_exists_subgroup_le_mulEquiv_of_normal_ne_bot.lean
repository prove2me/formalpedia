-- Prove2me | Theorems.Thm_CannonFloydParry_exists_subgroup_le_mulEquiv_of_normal_ne_bot
-- name    : CannonFloydParry.exists_subgroup_le_mulEquiv_of_normal_ne_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T12:06:05.669637+00:00
-- url     : https://prove2.me/theorems/ed33427e-70ae-4168-87b6-bfa48c94719b
-- title:
--   Every nontrivial normal subgroup of $F$ contains a copy of $F$
-- statement:
--   Let $N$ be a normal subgroup of Thompson's group $F$ with $N \ne \{1\}$. Then there is a
--   subgroup $H \le F$ with $H \subseteq N$ and $H$ isomorphic to $F$ as a group.
--
--   This is the sentence in the source's proof of Theorem 4.10, "Theorem 4.1 and Lemma 4.4 easily
--   imply that $N$ contains a subgroup isomorphic with $F$", stated on its own. The isomorphism is
--   only asserted to exist; no particular one is named.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, Theorem 4.10 (proof), p. 233.

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

/-- Theorem 4.10, the step the source states in words: every nontrivial normal subgroup of `F`
contains a subgroup isomorphic to `F`. -/
theorem exists_subgroup_le_mulEquiv_of_normal_ne_bot (N : Subgroup F) [N.Normal] (hN : N ≠ ⊥) :
    ∃ H : Subgroup F, H ≤ N ∧ Nonempty (H ≃* F) := by
  sorry

end CannonFloydParry
