-- Prove2me | Theorems.Thm_BlockCycleRotation_R_isBigO
-- name    : BlockCycleRotation.R_isBigO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:54.534444+00:00
-- url     : https://prove2.me/theorems/a83e01b1-b8dc-4058-8649-e1b1bbd98674
-- title:
--   $R(n) = C n^2 + O(n^{3/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$ there is $K>0$ with
--   $$\bigl| R(n) - C\,n^2 \bigr| \le K\,n^{3/2+\varepsilon} \qquad (n \ge 1).$$
--
--   $R(n)$ counts the coprime quadruples, $Q(n)$ all of them, and the two are related by $Q(n) = \sum_{d\mid n} R(d)$. Möbius inversion against the divisor sum $\sum_{d\mid n} d^{-2}$ converts the estimate for $Q$ into this one, which is the shape needed for Theorem 14.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 14. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L775-L830

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.R_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((Rquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2| ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by sorry
