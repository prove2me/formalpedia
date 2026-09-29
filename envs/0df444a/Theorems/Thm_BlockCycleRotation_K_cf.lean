-- Prove2me | Theorems.Thm_BlockCycleRotation_K_cf
-- name    : BlockCycleRotation.K_cf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:11.818406+00:00
-- url     : https://prove2.me/theorems/9bdf9752-59e4-494a-8ac1-910557384a8e
-- title:
--   Heilbronn's correspondence, inverse direction
-- statement:
--   **Heilbronn's correspondence, inverse direction.** Every coprime pair `a > a' ≥ 1` is `(K l, K l.dropLast)` for the expansion `l = cf a a'`.
--
--   In Blomer–Bux this is **Heilbronn 1969**, “Heilbronn, inverse direction”. It is used in the proofs of `heilbronn_bijection`, `heilbronn_surjective`, `quadExpansion_spec`, `remSum_eq_sum_K`, and 3 further result(s).
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Heilbronn 1969. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L245-L288

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.K_cf : ∀ a' a : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
    K (cf a a') = a ∧ K (cf a a').dropLast = a' := by sorry
