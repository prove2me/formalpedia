-- Prove2me | Theorems.Thm_BlockCycleRotation_remSum_congr_mod
-- name    : BlockCycleRotation.remSum_congr_mod
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:35.263441+00:00
-- url     : https://prove2.me/theorems/980cec5c-1d68-427f-9778-c93250a5c00c
-- title:
--   Lemma 11: $\operatorname{remSum}$ depends on the first argument only modulo the second
-- statement:
--   If $n \equiv m \pmod{k}$ then
--   $$\operatorname{remSum}(n,k) = \operatorname{remSum}(m,k).$$
--
--   This is the content of the induction in the paper's proof of Lemma 11. The block cycle recursion and the Euclidean algorithm do not keep the same first component — the algorithm carries a segment length, Euclid carries a remainder — but the two agree modulo the second component, so they emit the same sequence of remainders and hence the same remainder sum.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 11. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean#L84-L95

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.remSum_congr_mod {n m k : ℕ} (h : n % k = m % k) : remSum n k = remSum m k := by sorry
