-- Prove2me | Theorems.Thm_BlockCycleRotation_gtBound_bulk_eq
-- name    : BlockCycleRotation.gtBound_bulk_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:51.881046+00:00
-- url     : https://prove2.me/theorems/62b2207a-4083-460d-a90f-062609ec097e
-- title:
--   For a bulk pair the first branch of the cut-off wins
-- statement:
--   **For a bulk pair the first branch of the cut-off wins.** `Y = min(m/(a+a'), (m - d a²)/a')`, and the paper observes that the first term is the smaller exactly when `d·a·(a+a') ≤ m`. In the floored form used here that reads `gtBound m d a a' = (m-1)/(a+a') + 1`.
--
--   In Blomer–Bux this is **Lemmas 16 and 18**, “Cut-off on the bulk branch”. It is used in the proofs of `abs_G2term_le`, `bulk_pair_estimate`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L786-L822

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.gtBound_bulk_eq {m d a a' : ℕ} (hd : 0 < d) (ha' : 1 ≤ a') (haa : a' < a)
    (hbulk : d * a * (a + a') ≤ m) :
    gtBound m d a a' = (m - 1) / (a + a') + 1 := by sorry
