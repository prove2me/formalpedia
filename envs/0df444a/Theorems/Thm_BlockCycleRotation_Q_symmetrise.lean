-- Prove2me | Theorems.Thm_BlockCycleRotation_Q_symmetrise
-- name    : BlockCycleRotation.Q_symmetrise
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:19.083849+00:00
-- url     : https://prove2.me/theorems/156dc0d2-a7b6-4420-9987-d80a5da4fadb
-- title:
--   The symmetrisation
-- statement:
--   **The symmetrisation.** `Q(n)` splits into the part with `b > a` and the diagonal.
--
--   In Blomer–Bux this is **§4**, “Symmetrisation `b > a`”. It is used in the proof of `Q_isBigO`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L425-L468

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.Q_symmetrise (n : ℕ) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = (∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1))
        + ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 := by sorry
