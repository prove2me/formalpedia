-- Prove2me | Theorems.Thm_BlockCycleRotation_split_quadruple
-- name    : BlockCycleRotation.split_quadruple
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:46.251137+00:00
-- url     : https://prove2.me/theorems/bac2ae5d-3702-48e9-8f29-50cf93aeb30c
-- title:
--   The quadruple produced by a split
-- statement:
--   **The quadruple produced by a split.** For a shift `k` the algorithm recurses on and an interior split point `j`, the four continuants satisfy every condition defining Heilbronn's target set.
--
--   In Blomer–Bux this is **§4**, “Splits produce quadruples”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L626-L666

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.split_quadruple {n k j : ℕ} (hk : k ∈ shifts n) (hj1 : 1 ≤ j)
    (hj2 : j < (cf n k).length) :
    n = K ((cf n k).take j) * K ((cf n k).drop j)
        + K ((cf n k).take j).dropLast * K ((cf n k).drop j).tail
      ∧ 1 ≤ K ((cf n k).take j).dropLast
      ∧ K ((cf n k).take j).dropLast < K ((cf n k).take j)
      ∧ 1 ≤ K ((cf n k).drop j).tail
      ∧ K ((cf n k).drop j).tail < K ((cf n k).drop j)
      ∧ Nat.gcd (K ((cf n k).take j)) (K ((cf n k).take j).dropLast) = 1
      ∧ Nat.gcd (K ((cf n k).drop j)) (K ((cf n k).drop j).tail) = 1 := by sorry
