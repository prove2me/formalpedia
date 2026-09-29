-- Prove2me | Theorems.Thm_BlockCycleRotation_remSum_eq_sum_K
-- name    : BlockCycleRotation.remSum_eq_sum_K
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:41.506422+00:00
-- url     : https://prove2.me/theorems/31412dd5-e3b2-40d8-ae1b-b55cd7c348df
-- title:
--   Equation (eq. RemainderSum)
-- statement:
--   **Equation (eq. RemainderSum).** For coprime `n > k ≥ 1`, `remSum n k = ∑_{j < |cf n k|} K ((cf n k).take j)`. The remainders in the Euclidean algorithm are the continuants of the prefixes of the expansion.
--
--   In Blomer–Bux this is **Eq. (RemainderSum)**, “Eq. (RemainderSum): the bridge”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Eq. (RemainderSum). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L437-L477

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.remSum_eq_sum_K : ∀ k n : ℕ, 1 ≤ k → k < n → Nat.gcd n k = 1 →
    remSum n k = ∑ j ∈ Finset.range (cf n k).length, K ((cf n k).take j) := by sorry
