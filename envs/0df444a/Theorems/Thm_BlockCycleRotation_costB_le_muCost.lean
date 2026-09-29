-- Prove2me | Theorems.Thm_BlockCycleRotation_costB_le_muCost
-- name    : BlockCycleRotation.costB_le_muCost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:06:37.101215+00:00
-- url     : https://prove2.me/theorems/889c1638-f4f8-4297-877b-76f6eb61e5f2
-- title:
--   Corollary 6(3): the buffered algorithm never exceeds $\mu$
-- statement:
--   For $0 < n$, $0 < b$ and $2k \le n$,
--   $$m(n,k,b) \le \mu(n,k,b),$$
--   where $m(n,k,b)$ is the number of moves the buffered algorithm performs and $\mu$ is the continuous upper bound of equation (integral).
--
--   This is **Corollary 6(3)**. The paper states items (1) and (2) of that corollary for $\mu(\nu,\kappa,\beta)$ and then applies item (3) at $(n,k,b)$; the buffer argument here is $b$, not the relative $\beta$ of the earlier items.
--
--   The two recursions agree step for step; the inequality rather than equality comes from the algorithm's extra base case at $k = 0$, where it is already done while $\mu$ still charges its terminating branch.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Corollary 6(3). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L627-L667

import Definitions.Def_BlockCycleRotation_Buffer
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.costB_le_muCost : ∀ k n b : ℕ, 0 < n → 0 < b → 2 * k ≤ n →
    ((costB n k b : ℕ) : ℝ) ≤ muCost (n : ℝ) (k : ℝ) (b : ℝ) := by sorry
