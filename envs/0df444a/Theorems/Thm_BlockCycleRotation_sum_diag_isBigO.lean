-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_diag_isBigO
-- name    : BlockCycleRotation.sum_diag_isBigO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:11.830255+00:00
-- url     : https://prove2.me/theorems/4a26d6ee-af0e-4c9c-8ad4-7bf30d998a28
-- title:
--   The diagonal is `O(n^{1+ε})`
-- statement:
--   **The diagonal is `O(n^{1+ε})`.** This is the term the paper discards after symmetrising.
--
--   In Blomer–Bux this is **§4**, “Diagonal is `O(n^{1+ε})`”. It is used in the proof of `Q_isBigO`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L537-L593

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_diag_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε) := by sorry
