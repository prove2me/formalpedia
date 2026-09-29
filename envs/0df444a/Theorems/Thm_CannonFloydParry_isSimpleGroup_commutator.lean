-- Prove2me | Theorems.Thm_CannonFloydParry_isSimpleGroup_commutator
-- name    : CannonFloydParry.isSimpleGroup_commutator
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:31:56.058919+00:00
-- url     : https://prove2.me/theorems/3f177553-0965-4525-8fa3-1ae52396e7c2
-- title:
--   The commutator subgroup of $F$ is simple
-- statement:
--   The commutator subgroup $[F,F]$ of Thompson's group $F$ is a simple group: it is
--   nontrivial, and its only normal subgroups are the trivial subgroup and the whole of $[F,F]$.
--   Normality here is relative to $[F,F]$ itself, not to $F$.
--
--   Together with Theorem 4.3 this determines the entire normal subgroup lattice of $F$: a normal
--   subgroup of $F$ is either trivial or contains $[F,F]$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Theorem 4.5, p. 230

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem isSimpleGroup_commutator : IsSimpleGroup (commutator F) := by
  sorry

end CannonFloydParry
