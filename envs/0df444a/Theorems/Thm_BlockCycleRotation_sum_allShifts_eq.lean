-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_allShifts_eq
-- name    : BlockCycleRotation.sum_allShifts_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:20.568313+00:00
-- url     : https://prove2.me/theorems/af100827-b486-475c-a681-de2b0fc19364
-- title:
--   Classifying shifts by their gcd with `n`
-- statement:
--   **Classifying shifts by their gcd with `n`.** Every shift is `g·k'` for a unique divisor `g` of `n` and a shift `k'` of `n/g` coprime to it.
--
--   In Blomer–Bux this is **§4**, “Shifts classified by `gcd(n,k)`”. It is used in the proof of `sum_remSum_allShifts`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L944-L996

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_allShifts_eq {n : ℕ} (hn : 0 < n) (F : ℕ → ℕ → ℕ) :
    ∑ k ∈ allShifts n, F (Nat.gcd n k) (k / Nat.gcd n k)
      = ∑ g ∈ n.divisors, ∑ k' ∈ shifts (n / g), F g k' := by sorry
