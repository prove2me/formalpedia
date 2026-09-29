-- Prove2me | Theorems.Thm_FanoUnique_two_completions
-- name    : FanoUnique.two_completions
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T19:22:15.74104+00:00
-- url     : https://prove2.me/theorems/38aec560-6af8-458d-80f2-558c3a4103ba
-- title:
--   The two completions of $\{0,1,2\}, \{0,3,4\}, \{0,5,6\}$
-- statement:
--   Let $S$ be a Steiner triple system on $\{0, \dots, 6\}$ whose lines include $\{0,1,2\}$, $\{0,3,4\}$ and $\{0,5,6\}$. Then its lines are exactly one of
--
--   $$
--   \text{A: } \{0,1,2\}, \{0,3,4\}, \{0,5,6\}, \{1,3,6\}, \{1,4,5\}, \{2,3,5\}, \{2,4,6\},
--   $$
--
--   $$
--   \text{B: } \{0,1,2\}, \{0,3,4\}, \{0,5,6\}, \{1,3,5\}, \{1,4,6\}, \{2,3,6\}, \{2,4,5\}.
--   $$
--
--   The line through $1$ and $3$ is $\{1,3,5\}$ or $\{1,3,6\}$, and that choice forces the other three lines.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3, proof of Theorem 3.3 ("Uniqueness of STS(7) is classical"); this is a step of the standard textbook proof, supplying the step C1 calls classical: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; public references: Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Steiner system": https://en.wikipedia.org/wiki/Steiner_system

import Mathlib
import Definitions.Def_FanoUnique_isFano

namespace FanoUnique

open RolesForceSeven

theorem two_completions (S : STS 7)
    (h₁ : ({0, 1, 2} : Finset (Fin 7)) ∈ S.lines) (h₂ : ({0, 3, 4} : Finset (Fin 7)) ∈ S.lines)
    (h₃ : ({0, 5, 6} : Finset (Fin 7)) ∈ S.lines) :
    S.lines = {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 6}, {1, 4, 5}, {2, 3, 5}, {2, 4, 6}} ∨
    S.lines = {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}} := by
  sorry

end FanoUnique
