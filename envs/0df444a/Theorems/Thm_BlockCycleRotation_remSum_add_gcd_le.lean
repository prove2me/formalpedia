-- Prove2me | Theorems.Thm_BlockCycleRotation_remSum_add_gcd_le
-- name    : BlockCycleRotation.remSum_add_gcd_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:50:49.619444+00:00
-- url     : https://prove2.me/theorems/78ca224b-e4b1-4aaf-bec5-546942e9b3ea
-- title:
--   Master inequality
-- statement:
--   **Master inequality.** For all `n` and `k`, `remSum n k + gcd n k ≤ 2 * k + n % k`. This is the inductive engine behind the worst-case analysis. Note it holds unconditionally, including for `k = 0` (where both sides equal `n`).
--
--   The paper uses this step without giving it a number; the formalization records it as “Master inequality”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Euclid.lean#L55-L87

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.remSum_add_gcd_le : ∀ k n : ℕ, remSum n k + Nat.gcd n k ≤ 2 * k + n % k := by sorry
