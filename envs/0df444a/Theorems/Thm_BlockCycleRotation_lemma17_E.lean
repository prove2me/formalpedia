-- Prove2me | Theorems.Thm_BlockCycleRotation_lemma17_E
-- name    : BlockCycleRotation.lemma17_E
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:10.010088+00:00
-- url     : https://prove2.me/theorems/405773f9-9bab-4a4e-956c-e32ac8de2a86
-- title:
--   The per-divisor error bound holds
-- statement:
--   **The per-divisor error bound holds.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `lemma17_final`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L580-L597

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.lemma17_E {n : ℕ} (hn : 0 < n) (d : ℕ) (hd : d ∈ n.divisors) :
    |(∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
          ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
            + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
        - ((n / d : ℕ) : ℝ) ^ 2 * cConst| ≤ Eterm n d := by sorry
