-- Prove2me | Theorems.Thm_BlockCycleRotation_costB_eq_moveCount
-- name    : BlockCycleRotation.costB_eq_moveCount
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:37.483226+00:00
-- url     : https://prove2.me/theorems/9e346080-5dfb-42cc-94f7-dbdeb3d242f0
-- title:
--   Consistency of the two cost models
-- statement:
--   **Consistency of the two cost models.** With no buffer, equation (integral) computes exactly the move count `n - gcd(n,k) + 2·remSum(n,k)` of Lemma 11.
--
--   In Blomer–Bux this is **§2–3**, “Eq. (integral) at `β = 0` is Lemma 11”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §2–3. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L669-L703

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.costB_eq_moveCount : ∀ k n : ℕ, 2 * k ≤ n → costB n k 0 = moveCount n k := by sorry
