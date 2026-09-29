-- Prove2me | Theorems.Thm_FanoUnique_normal_form
-- name    : FanoUnique.normal_form
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T19:21:39.260924+00:00
-- url     : https://prove2.me/theorems/2dc9a819-58f3-4916-a1c8-4b52797f859c
-- title:
--   Normal form: the lines through $0$ can be made $\{0,1,2\}, \{0,3,4\}, \{0,5,6\}$
-- statement:
--   Let $S$ be a Steiner triple system on $\{0, \dots, 6\}$. There is a permutation $e$ of $\{0, \dots, 6\}$ such that, after relabelling every point $x$ as $e(x)$, the three sets
--
--   $$
--   \{0,1,2\}, \qquad \{0,3,4\}, \qquad \{0,5,6\}
--   $$
--
--   are lines. The three lines through any point split the other six points into three pairs; send the point to $0$ and the pairs to $\{1,2\}, \{3,4\}, \{5,6\}$.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3, proof of Theorem 3.3 ("Uniqueness of STS(7) is classical"); this is a step of the standard textbook proof, supplying the step C1 calls classical: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; public references: Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Steiner system": https://en.wikipedia.org/wiki/Steiner_system

import Mathlib
import Definitions.Def_FanoUnique_isFano

namespace FanoUnique

open RolesForceSeven

theorem normal_form (S : STS 7) :
    ∃ e : Fin 7 ≃ Fin 7,
      ({0, 1, 2} : Finset (Fin 7)) ∈ S.lines.image (fun l => l.map e.toEmbedding) ∧
      ({0, 3, 4} : Finset (Fin 7)) ∈ S.lines.image (fun l => l.map e.toEmbedding) ∧
      ({0, 5, 6} : Finset (Fin 7)) ∈ S.lines.image (fun l => l.map e.toEmbedding) := by
  sorry

end FanoUnique
