-- Prove2me | Theorems.Thm_CannonFloydParry_existsUnique_tree_marks_eq
-- name    : CannonFloydParry.existsUnique_tree_marks_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:08:58.680375+00:00
-- url     : https://prove2.me/theorems/c4f5ed01-801a-4e96-a8d0-3170739c8516
-- title:
--   Standard dyadic partitions correspond to $\mathcal{T}$-trees
-- statement:
--   For every standard dyadic partition of $[0,1]$ there is **exactly one** ordered rooted
--   binary tree whose leaves cut out that partition.
--
--   Together with the previous statement this is the canonical bijection between standard dyadic
--   partitions and $\mathcal{T}$-trees: the map sending a tree to its breakpoint list is injective
--   and its image is precisely the standard dyadic partitions.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 220 (the converse half, completing the canonical bijection)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem existsUnique_tree_marks_eq {xs : List ℝ} (h : IsStandardDyadicPartition xs) :
    ∃! t : TTree, t.marks = xs := by
  sorry

end CannonFloydParry
