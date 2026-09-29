-- Prove2me | Theorems.Thm_BlockCycleRotation_remSum_fib
-- name    : BlockCycleRotation.remSum_fib
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:22.346642+00:00
-- url     : https://prove2.me/theorems/4f642f69-7764-4e19-91be-55f575de49bd
-- title:
--   Observation 3: the remainder sum on the Fibonacci family
-- statement:
--   For every $j$, with $n = F_{j+4}$ and $k = F_{j+2}$,
--   $$\operatorname{remSum}(n,k) = F_{j+4} - 2 = n-2 .$$
--
--   The Euclidean algorithm on consecutive Fibonacci numbers steps down the Fibonacci sequence, so its remainders telescope to $\sum_{j} F_j = F_{j+2}-1$. This is the arithmetic input to Observation 3; combined with Lemma 11(2) with equation (7) it yields the $3n-5$ move count.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Obs. 3. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean#L222-L264

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.remSum_fib (j : ℕ) :
    remSum (Nat.fib (j + 4)) (Nat.fib (j + 2)) = Nat.fib (j + 4) - 2 := by sorry
