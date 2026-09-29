-- Prove2me | Theorems.Thm_CannonFloydParry_mul_comm_quotient_of_ne_bot
-- name    : CannonFloydParry.mul_comm_quotient_of_ne_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:30:00.02045+00:00
-- url     : https://prove2.me/theorems/f1d391d0-cd08-45e1-9868-f4e84d901daf
-- title:
--   Every proper quotient of $F$ is Abelian
-- statement:
--   Let $N$ be a normal subgroup of Thompson's group $F$ other than the trivial subgroup.
--   Then the quotient group $F/N$ is Abelian.
--
--   Equivalently, every nontrivial normal subgroup of $F$ contains the commutator subgroup. The
--   case $N = F$ is included and gives the one-element quotient. The source's proof uses the unique
--   normal form of Corollary-Definition 2.7, which this mission does not formalize.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Theorem 4.3, p. 229

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem mul_comm_quotient_of_ne_bot (N : Subgroup F) [N.Normal] (hN : N ≠ ⊥)
    (x y : F ⧸ N) : x * y = y * x := by
  sorry

end CannonFloydParry
