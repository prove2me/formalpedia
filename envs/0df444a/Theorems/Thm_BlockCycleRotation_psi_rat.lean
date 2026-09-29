-- Prove2me | Theorems.Thm_BlockCycleRotation_psi_rat
-- name    : BlockCycleRotation.psi_rat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:58.620802+00:00
-- url     : https://prove2.me/theorems/9121da39-f349-49c9-84cb-da4365d54304
-- title:
--   Lemma 11: $n\,\psi(k/n) = 2\,\operatorname{remSum}(n,k)$
-- statement:
--   Let $\psi : [0,\tfrac12] \to \mathbb{R}$ be the continuous-parameter cost function defined by the paper's recursion. For all $n > 0$ and $2k \le n$,
--   $$n\,\psi\!\left(\frac{k}{n}\right) = 2\,\operatorname{remSum}(n,k).$$
--
--   This is Lemma 11, the bridge between the arithmetic and the analytic halves of the paper. The discrete quantity on the right is what the Euclidean algorithm produces; the function $\psi$ on the left is defined by a self-similar recursion on the reals and is the object whose continuity and integrability Theorem 7 establishes.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 11(2). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L258-L296

import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.psi_rat : ∀ k : ℕ, ∀ n : ℕ, 0 < n → 2 * k ≤ n →
    (n : ℝ) * psi ((k : ℝ) / (n : ℝ)) = 2 * (remSum n k : ℝ) := by sorry
