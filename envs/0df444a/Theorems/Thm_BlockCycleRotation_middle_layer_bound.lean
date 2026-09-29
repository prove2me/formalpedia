-- Prove2me | Theorems.Thm_BlockCycleRotation_middle_layer_bound
-- name    : BlockCycleRotation.middle_layer_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:20.596374+00:00
-- url     : https://prove2.me/theorems/389d928a-9df1-4df9-ac71-e373e38cc650
-- title:
--   The middle layer
-- statement:
--   **The middle layer.** Summing the per-pair error bound over the coprime pairs gives `3m(1 + log m)` for each admissible `a`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `middle_layer`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L996-L1042

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.middle_layer_bound {m d : ℕ} (hm : 0 < m) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
        (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / p.1) * (1 + Real.log m)
      ≤ (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ)
          * (3 * (m : ℝ) * (1 + Real.log m)) := by sorry
