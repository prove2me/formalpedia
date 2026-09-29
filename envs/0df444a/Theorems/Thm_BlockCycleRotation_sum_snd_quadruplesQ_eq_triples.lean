-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_snd_quadruplesQ_eq_triples
-- name    : BlockCycleRotation.sum_snd_quadruplesQ_eq_triples
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:14:00.388176+00:00
-- url     : https://prove2.me/theorems/c005e48a-d382-4678-97ee-04fe5db37e23
-- title:
--   The `b`-elimination
-- statement:
--   **The `b`-elimination.** `Q(n)` as a sum over triples.
--
--   In Blomer–Bux this is **§4**, “`b`-elimination to triples”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L116-L155

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_snd_quadruplesQ_eq_triples {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1 = ∑ t ∈ triples n, (n - t.2.1 * t.2.2) / t.1 := by sorry
