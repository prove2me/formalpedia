-- Prove2me | Theorems.Thm_BlockCycleRotation_lemma17_isBigO
-- name    : BlockCycleRotation.lemma17_isBigO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:24.913368+00:00
-- url     : https://prove2.me/theorems/cb4736b5-20ca-4818-bed6-0592ee88ba21
-- title:
--   Lemma 19 in the paper's form: error $O(n^{3/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$ there is $K>0$ with
--   $$\left| G_1(n) - C\,n^2 \sum_{d\mid n} \frac{1}{d^2} \right| \le K\,n^{3/2+\varepsilon}.$$
--
--   This is Lemma 19 as stated in the paper. It follows from the instantiated form by bounding each per-divisor error by $(8+2C)n^{3/2}$ and the number of divisors by $O(n^{\varepsilon})$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L743-L765

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.lemma17_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by sorry
