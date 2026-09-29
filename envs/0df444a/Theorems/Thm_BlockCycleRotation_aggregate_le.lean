-- Prove2me | Theorems.Thm_BlockCycleRotation_aggregate_le
-- name    : BlockCycleRotation.aggregate_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:11.916363+00:00
-- url     : https://prove2.me/theorems/70c9edd0-a274-4dfa-9252-193273856ea3
-- title:
--   A per-pair bound of size `W·(1 + log m)` aggregates to `Err n`
-- statement:
--   A per-pair bound of size `W·(1 + log m)` aggregates to `Err n`. This is the middle and outer layer, applied to whichever of `G₂`, `G₃` is at hand.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `abs_G3sum_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L454-L493

import Definitions.Def_BlockCycleRotation_Theorem13
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.aggregate_le {n : ℕ} (hn : 0 < n) (F : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ d ∈ n.divisors, ∀ p ∈ (coprimePairs (n / d)).filter
        (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
      |F (n / d) d p.1 p.2|
        ≤ (((d * p.1 : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (p.1 : ℝ))
            * (1 + Real.log ((n / d : ℕ) : ℝ))) :
    |∑ d ∈ n.divisors, ∑ p ∈ (coprimePairs (n / d)).filter
        (fun p => d * p.1 * (p.1 + p.2) ≤ n / d), F (n / d) d p.1 p.2| ≤ Err n := by sorry
