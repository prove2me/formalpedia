-- Prove2me | Theorems.Thm_BlockCycleRotation_moebius_main
-- name    : BlockCycleRotation.moebius_main
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:43.776173+00:00
-- url     : https://prove2.me/theorems/01d57b6f-7bac-4036-9d9d-83f900643e5e
-- title:
--   The main term after Möbius inversion
-- statement:
--   **The main term after Möbius inversion.**
--
--   In Blomer–Bux this is **Thm 14**, “Möbius inversion of `∑_{d∣n} d²`”. It is used in the proof of `R_isBigO`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 14. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L747-L773

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.moebius_main {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2)
      = cConst * (n : ℝ) ^ 2 := by sorry
