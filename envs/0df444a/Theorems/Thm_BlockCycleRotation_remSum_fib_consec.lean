-- Prove2me | Theorems.Thm_BlockCycleRotation_remSum_fib_consec
-- name    : BlockCycleRotation.remSum_fib_consec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:58.841279+00:00
-- url     : https://prove2.me/theorems/f47f63aa-9125-4769-93f5-59cf3d8ed24a
-- title:
--   Consecutive Fibonacci numbers: `remSum F_{m+1} F_m = F_{m+2} - 2` for `m ≥ 2`
-- statement:
--   Consecutive Fibonacci numbers: `remSum F_{m+1} F_m = F_{m+2} - 2` for `m ≥ 2`.
--
--   In Blomer–Bux this is **Obs. 3**, “`remSum F_{m+1} F_m = F_{m+2} − 2`”. It is used in the proof of `remSum_fib`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Obs. 3. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean#L193-L220

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.remSum_fib_consec : ∀ j : ℕ, remSum (Nat.fib (j + 3)) (Nat.fib (j + 2)) =
    Nat.fib (j + 4) - 2 := by sorry
