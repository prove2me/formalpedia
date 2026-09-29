-- Prove2me | Theorems.Thm_BlockCycleRotation_Q_eq_tripleSum_decomposed
-- name    : BlockCycleRotation.Q_eq_tripleSum_decomposed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:26.529725+00:00
-- url     : https://prove2.me/theorems/2dd89380-5a8c-4f12-9d35-f50b90b87aea
-- title:
--   The triple sum in estimable form
-- statement:
--   **The triple sum in estimable form.** `Q(n)` as a sum over divisors `d ∣ n`, coprime pairs `(a, a')`, and `b'` in an initial segment filtered by the divisibility condition. By `inner_sum_nat_eq` the innermost sum is an arithmetic-progression sum of a linear function, which `inner_sum_sub_main_le` estimates.
--
--   In Blomer–Bux this is **§4**, “Triple sum decomposed by pairs”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L356-L372

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.Q_eq_tripleSum_decomposed {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ p ∈ coprimePairs (n / d),
          ∑ b' ∈ (Finset.Ico 1 (bBound (n / d) p.1 p.2)).filter
            (fun b' => p.1 ∣ (n / d - p.2 * b')), (n / d - p.2 * b') / p.1 := by sorry
