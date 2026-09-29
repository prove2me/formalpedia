-- Prove2me | Theorems.Thm_BlockCycleRotation_gtTriples_bulk_decompose
-- name    : BlockCycleRotation.gtTriples_bulk_decompose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:56.540886+00:00
-- url     : https://prove2.me/theorems/72eb22b2-a2ca-4800-873d-3844e73a0cb3
-- title:
--   The bulk part of the triple sum, decomposed by pairs
-- statement:
--   **The bulk part of the triple sum, decomposed by pairs.**
--
--   In Blomer–Bux this is **Lemmas 16 and 18**, “Bulk triple sum, by pairs”. It is used in the proof of `divisor_estimate`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L315-L355

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.gtTriples_bulk_decompose {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (d * p.1 + (m - p.2 * b') / p.1) := by sorry
