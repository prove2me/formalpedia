-- Prove2me | Theorems.Thm_BlockCycleRotation_Q_isBigO
-- name    : BlockCycleRotation.Q_isBigO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:38.274578+00:00
-- url     : https://prove2.me/theorems/89219f0c-70d7-4ced-9549-687c4a0897e9
-- title:
--   $Q(n) = C n^2 \sum_{d \mid n} d^{-2} + O(n^{3/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$ there is $K>0$ with
--   $$\left| Q(n) - C\,n^2 \sum_{d \mid n} \frac{1}{d^2} \right| \le K\,n^{3/2+\varepsilon} \qquad (n \ge 1),$$
--   where $C$ is the constant of equation (const-c).
--
--   This is the asymptotic evaluation of the quadruple sum, assembled from Lemma 19 (which produces the main term $G_1$) and Lemmas 16 and 18 (which bound the oscillating parts $G_2$ and $G_3$). It is the last step before Möbius inversion turns $Q$ into $R$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 14. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L695-L740

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.Q_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((Qquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by sorry
