-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_remSum_isBigO
-- name    : BlockCycleRotation.sum_remSum_isBigO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:48.954558+00:00
-- url     : https://prove2.me/theorems/c89b2817-45af-4f7b-bfe1-8de922b5bf17
-- title:
--   $\sum_{2k \le n} \operatorname{remSum}(n,k) = C n^2 + O(n^{3/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$ there is $K>0$ with
--   $$\left| \sum_{k \in \mathrm{Sh}(n)} \operatorname{remSum}(n,k) \;-\; C\,n^2 \right| \le K\,n^{3/2+\varepsilon}.$$
--
--   This is the arithmetic statement that Theorem 14 rests on: the total remainder sum over all shifts the algorithm recurses on is $Cn^2$ to within $O(n^{3/2+\varepsilon})$. Passing to move counts through Lemma 11(2) with equation (7) and dividing by $n$ turns it into the average-cost asymptotic with $D = 1+4C$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 14. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L837-L874

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.sum_remSum_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ) - cConst * (n : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by sorry
