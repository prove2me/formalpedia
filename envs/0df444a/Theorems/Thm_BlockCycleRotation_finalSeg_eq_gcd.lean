-- Prove2me | Theorems.Thm_BlockCycleRotation_finalSeg_eq_gcd
-- name    : BlockCycleRotation.finalSeg_eq_gcd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:45.64627+00:00
-- url     : https://prove2.me/theorems/22d0d119-e035-4379-85aa-18c7d9e2ef9a
-- title:
--   Lemma 11(1): the recursion terminates at $\gcd(n,k)$
-- statement:
--   The block cycle recursion on $(n,k)$ terminates on a subproblem whose parameters are $(\gcd(n,k),\,0)$:
--   $$\operatorname{finalSeg}(n,k) = \gcd(n,k).$$
--
--   This is part (1) of Lemma 11. Together with the identification of the intermediate segment lengths with Euclidean remainders it gives the paper's dictionary between the algorithm's recursion and the Euclidean algorithm, and it supplies the $\gcd(n,k)$ appearing in Lemma 11(2) with equation (7).
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 11. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean#L103-L113

import Definitions.Def_BlockCycleRotation_Algorithm
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.finalSeg_eq_gcd : ∀ k n : ℕ, finalSeg n k = Nat.gcd n k := by sorry
