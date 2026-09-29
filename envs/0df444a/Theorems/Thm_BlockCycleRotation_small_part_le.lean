-- Prove2me | Theorems.Thm_BlockCycleRotation_small_part_le
-- name    : BlockCycleRotation.small_part_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:27.277785+00:00
-- url     : https://prove2.me/theorems/27d70953-2e24-48bf-bd95-0f9ddd8c3e0c
-- title:
--   The small part is $O(m^{3/2}\sqrt d)$
-- statement:
--   The contribution of the triples violating the bulk condition satisfies
--   $$\sum_{\substack{t \in \mathcal{T}^{>}(m,d) \\ d\,a(a+a') > m}} \left( d\,a + \left\lfloor\frac{m-a'b'}{a}\right\rfloor \right) \le \left(\sqrt{\tfrac{m-1}{d}}+1\right)(2d+2)(2m).$$
--
--   Outside the bulk the inner sum is too short for the progression estimate to help, so it is bounded trivially; the constraint $2da^2 > m$ limits how many pairs can be in this regime, and the crude bound is still $O(m^{3/2}\sqrt d)$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1354-L1403

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.small_part_le {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      ≤ (Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) := by sorry
