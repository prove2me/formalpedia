-- Prove2me | Theorems.Thm_BlockCycleRotation_excluded_pair_large
-- name    : BlockCycleRotation.excluded_pair_large
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:15.722372+00:00
-- url     : https://prove2.me/theorems/90085979-251a-4573-9ed1-959880ea51d8
-- title:
--   Pairs outside the bulk have large `a`
-- statement:
--   **Pairs outside the bulk have large `a`.** If `d·a·(a+a') > m` then `2d·a² > m`, so `a > √(m/(2d))`. This is what makes the truncation of the series for `C` cost only `O(√(d/m))`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1430-L1435

import Mathlib

open Real Finset

theorem BlockCycleRotation.excluded_pair_large {m d a a' : ℕ} (ha' : 1 ≤ a') (haa : a' < a)
    (h : m < d * a * (a + a')) : m < 2 * d * (a * a) := by sorry
