-- Prove2me | Theorems.Thm_BlockCycleRotation_remark_all_shifts
-- name    : BlockCycleRotation.remark_all_shifts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:22.248701+00:00
-- url     : https://prove2.me/theorems/b3c3dd82-0615-477a-90d8-e47a282c9622
-- title:
--   The average over all shifts $1 \le k \le n$
-- statement:
--   For every $\varepsilon>0$ there is $K>0$ with
--   $$\left| \frac{1}{n}\sum_{k=1}^{n} \operatorname{remSum}(n,k) - \left(\frac38 + 2C\right) n \right| \le K\,n^{1/2+\varepsilon}.$$
--
--   The remark following Theorem 14. The main theorems average over the shifts $2k \le n$ that the algorithm actually recurses on; averaging over *all* shifts adds the reflected range, which by $\operatorname{remSum}(n,k) = k + \operatorname{remSum}(n,n-k)$ contributes the explicit $\sum_{k>n/2}k = \tfrac38 n^2 + O(n)$ — hence the extra $3/8$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 20. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/AllShifts.lean#L211-L244

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Filter Topology Finset Real

theorem BlockCycleRotation.remark_all_shifts {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((∑ k ∈ Finset.Icc 1 n, remSum n k : ℕ) : ℝ) / (n : ℝ)
          - (3 / 8 + 2 * cConst) * (n : ℝ)|
        ≤ K * (n : ℝ) ^ (1 / 2 + ε) := by sorry
