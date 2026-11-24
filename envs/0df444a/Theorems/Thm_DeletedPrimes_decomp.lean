-- Prove2me | Theorems.Thm_DeletedPrimes_decomp
-- name    : DeletedPrimes.decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:30.202778+00:00
-- url     : https://prove2.me/theorems/aa492a7a-826e-4868-b672-6b2fb14e4f26
-- title:
--   Deleted Primes: decomp
-- statement:
--   Division of `j ∈ [0, k u]` by the unit `u`, with the remainder compared to `α u`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L90-L115
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L90-L115

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.decomp {u j α : ℝ} {k : ℕ} (hα : 0 < α) (hu : 0 ≤ u) (hj0 : 0 ≤ j) (hjk : j ≤ k * u) :
    ∃ n : ℕ, n ≤ k ∧ (n : ℝ) * u ≤ j ∧
      (j - n * u ≤ α * u ∨ (α * u < j - n * u ∧ j < ((n : ℝ) + 1) * u ∧ n + 1 ≤ k)) := by sorry
