-- Prove2me | Theorems.Thm_BlockCycleRotation_theorem13
-- name    : BlockCycleRotation.theorem13
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:00.18375+00:00
-- url     : https://prove2.me/theorems/7b1354a7-4a7a-4471-9746-0d2e9d6c8885
-- title:
--   Theorem 14: $\operatorname{avgCost}(n) = D n + O(n^{1/2+\varepsilon})$, $D = 1+4C$
-- statement:
--   For every $\varepsilon>0$ there is $K>0$ such that for all $n \ge 1$
--   $$\bigl|\operatorname{avgCost}(n) - D\,n\bigr| \le K\,n^{1/2+\varepsilon}, \qquad D = 1+4C \approx 1.85 .$$
--
--   Theorem 14, the paper's main average-case result, and a strict sharpening of Theorem 9: not only does $\operatorname{avgCost}(n)/n$ converge, it converges to $D$ with a power-saving error term. The proof runs through the arithmetic side — Heilbronn's correspondence, the triple sum, Lemmas 16, 18 and 19 give $\sum_{k} \operatorname{remSum}(n,k) = Cn^2 + O(n^{3/2+\varepsilon})$ — and then converts remainder sums to move counts by Lemma 11(2) with equation (7).
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 14. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L977-L1059

import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.theorem13 {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |avgCost n - dConst * (n : ℝ)| ≤ K * (n : ℝ) ^ (1 / 2 + ε) := by sorry
