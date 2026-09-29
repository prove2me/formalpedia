-- Prove2me | Theorems.Thm_BlockCycleRotation_divisor_estimate
-- name    : BlockCycleRotation.divisor_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:15.06169+00:00
-- url     : https://prove2.me/theorems/562982aa-ca8b-4bac-aa08-9c7fde83f138
-- title:
--   The estimate at one divisor
-- statement:
--   For $m,d>0$ the triple sum at $d$ differs from the sum of the bulk main terms at $d$ by at most twice the middle-layer bound plus the small part. Combining the per-pair estimates over all coprime pairs at a fixed divisor, and adding the crude bound for the non-bulk triples, this is the last step before summing over $d \mid n$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L357-L442

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.divisor_estimate {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    |((∑ t ∈ gtTriples m d, (d * t.1 + (m - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ)
        - ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
            ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)|
      ≤ 2 * (((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * (3 * (m : ℝ) * (1 + Real.log m)))
        + (((Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) : ℕ) : ℝ) := by sorry
