-- Prove2me | Theorems.Thm_BlockCycleRotation_gtTriples_decompose
-- name    : BlockCycleRotation.gtTriples_decompose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:48.664576+00:00
-- url     : https://prove2.me/theorems/6329affe-0a04-44a0-a438-22bb1f421131
-- title:
--   The restricted triple sum, decomposed by pairs
-- statement:
--   **The restricted triple sum, decomposed by pairs.**
--
--   In Blomer–Bux this is **§4**, “Triple sum decomposed by pairs”. It is used in the proofs of `gtTriples_bulk_decompose`, `small_part_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L824-L858

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.gtTriples_decompose {m d : ℕ} (hm : 0 < m) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ gtTriples m d, f t.1 t.2.1 t.2.2
      = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter
            (fun b' => p.1 ∣ (m - p.2 * b')), f p.1 p.2 b' := by sorry
