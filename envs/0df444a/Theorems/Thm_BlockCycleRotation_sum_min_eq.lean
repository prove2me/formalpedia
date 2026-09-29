-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_min_eq
-- name    : BlockCycleRotation.sum_min_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:07.508117+00:00
-- url     : https://prove2.me/theorems/d31bd24b-61cf-40a4-93be-ce68a8a85b8d
-- title:
--   The double count
-- statement:
--   **The double count.**
--
--   In Blomer–Bux this is **Thm 14**, “Folding all shifts onto `2k ≤ n`”. It is used in the proof of `sum_gcd_range_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 14. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L896-L953

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.sum_min_eq {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) :
    (∑ k ∈ Finset.Ico 1 n, f (min k (n - k))) + (if 2 ∣ n then f (n / 2) else 0)
      = 2 * ∑ j ∈ allShifts n, f j := by sorry
