-- Prove2me | Theorems.Thm_BlockCycleRotation_gtBound_bulk
-- name    : BlockCycleRotation.gtBound_bulk
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:12.613171+00:00
-- url     : https://prove2.me/theorems/50d1c3be-4539-4fb1-bd2a-fd6ffabe2fb1
-- title:
--   On the bulk branch the range of `b'` is cut by `(a+a')·b' < m` alone
-- statement:
--   On the bulk branch the range of `b'` is cut by `(a+a')·b' < m` alone.
--
--   In Blomer–Bux this is **Lemma 19**, “Bulk/small split condition”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1198-L1210

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.gtBound_bulk {m d a a' : ℕ} (hm : 0 < m) (ha : 0 < a) (ha' : 0 < a')
    (hda : d * a * a < m) (hbulk : d * a * (a + a') ≤ m) :
    Finset.Ico 1 (gtBound m d a a') = Finset.Ico 1 ((m - 1) / (a + a') + 1) := by sorry
