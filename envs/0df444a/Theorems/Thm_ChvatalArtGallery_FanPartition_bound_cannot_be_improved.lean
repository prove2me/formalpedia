-- Prove2me | Theorems.Thm_ChvatalArtGallery_FanPartition_bound_cannot_be_improved
-- name    : ChvatalArtGallery.FanPartition.bound_cannot_be_improved
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:14:01.22723+00:00
-- url     : https://prove2.me/theorems/922e641c-5f61-416d-b3dd-a46d25a1c6b2
-- title:
--   p. 41 — the bound ⌊n/3⌋ cannot be improved: some n-triangulation needs ⌊n/3⌋ fans
-- statement:
--   For every $n \ge 3$ there is an $n$-triangulation $G$ (with set of inner edges $D$) such that every partition $P$ of $G$ into fans has at least $\lfloor n/3\rfloor$ members:
--   $$\forall n \ge 3\ \ \exists D\ \text{an } n\text{-triangulation}:\quad \forall P \text{ partition of } G \text{ into fans},\quad |P| \ge \lfloor n/3 \rfloor.$$
--
--   Chvátal remarks on p. 41 that "the bound $[n/3]$ in our theorem cannot be improved". Together with the main theorem this says that $\lfloor n/3\rfloor$ is exactly the largest, over all $n$-triangulations, of the least number of fans in a partition.
--
--   **Formalization Note.** The paper justifies the remark geometrically, through Klee's art-gallery function and the comb of Figure 1; the statement here is the combinatorial content of the remark about the theorem itself, with the quantifiers in the order "for every $n$ there is a triangulation such that every fan partition is large". $[n/3]$ is the floor, `n / 3` in ℕ. Triangulations and fan partitions are as in the mission's definition file.
-- source:
--   Chvátal, A combinatorial theorem in plane geometry, J. Combin. Theory Ser. B 18 (1975), p. 41, "Note also that the bound [n/3] in our theorem cannot be improved"

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- p. 41: the bound ⌊n/3⌋ cannot be improved — for every n ≥ 3 some n-triangulation admits no
partition into fewer than ⌊n/3⌋ fans. -/
theorem bound_cannot_be_improved (n : ℕ) (hn : 3 ≤ n) :
    ∃ D : Finset (Sym2 (Fin n)), IsTriangulation n D ∧
      ∀ P : Finset (Finset (Finset (Fin n))), IsFanPartition n D P → n / 3 ≤ P.card := by sorry

end ChvatalArtGallery.FanPartition
