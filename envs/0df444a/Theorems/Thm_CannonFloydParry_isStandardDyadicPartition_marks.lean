-- Prove2me | Theorems.Thm_CannonFloydParry_isStandardDyadicPartition_marks
-- name    : CannonFloydParry.isStandardDyadicPartition_marks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:08:13.866278+00:00
-- url     : https://prove2.me/theorems/5999fd87-cdcf-4f36-95f9-006e9e6f9f3c
-- title:
--   The leaves of a $\mathcal{T}$-tree cut out a standard dyadic partition
-- statement:
--   For every ordered rooted binary tree, the list of breakpoints obtained by giving
--   $[0,1]$ to the root and splitting each interval at its midpoint between the two children, down
--   to the leaves, is a standard dyadic partition of $[0,1]$.
--
--   That is: the list starts at $0$, ends at $1$, and every pair of consecutive entries is a
--   standard dyadic interval $[a/2^n, (a+1)/2^n]$. In particular the list increases, and its
--   intervals are exactly the intervals assigned to the leaves.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 220 (the forward half of the bijection with standard dyadic partitions)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem isStandardDyadicPartition_marks (t : TTree) :
    IsStandardDyadicPartition t.marks := by
  sorry

end CannonFloydParry
