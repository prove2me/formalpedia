-- Prove2me | Theorems.Thm_FanoUnique_completions_are_fano
-- name    : FanoUnique.completions_are_fano
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T19:23:13.827983+00:00
-- url     : https://prove2.me/theorems/dc74aad1-9e3d-4d63-9d2a-86f04281042f
-- title:
--   Both completions are the Fano plane
-- statement:
--   Let $S$ be a Steiner triple system on $\{0, \dots, 6\}$ whose lines are exactly completion A or exactly completion B:
--
--   $$
--   \text{A: } \{0,1,2\}, \{0,3,4\}, \{0,5,6\}, \{1,3,6\}, \{1,4,5\}, \{2,3,5\}, \{2,4,6\},
--   $$
--
--   $$
--   \text{B: } \{0,1,2\}, \{0,3,4\}, \{0,5,6\}, \{1,3,5\}, \{1,4,6\}, \{2,3,6\}, \{2,4,5\}.
--   $$
--
--   Then $S$ is the Fano plane up to relabelling: some permutation of the points carries its lines exactly onto $\{\{i, i+1, i+3\} : i \in \mathbb{Z}/7\}$. For A the permutation $0\mapsto0,\ 1\mapsto1,\ 2\mapsto3,\ 3\mapsto2,\ 4\mapsto6,\ 5\mapsto5,\ 6\mapsto4$ works.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3, proof of Theorem 3.3 ("Uniqueness of STS(7) is classical"); this is a step of the standard textbook proof, supplying the step C1 calls classical: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; public references: Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Steiner system": https://en.wikipedia.org/wiki/Steiner_system

import Mathlib
import Definitions.Def_FanoUnique_isFano

namespace FanoUnique

open RolesForceSeven

theorem completions_are_fano (S : STS 7)
    (h : S.lines = {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 6}, {1, 4, 5}, {2, 3, 5}, {2, 4, 6}} ∨
      S.lines = {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}) :
    IsFano S := by
  sorry

end FanoUnique
