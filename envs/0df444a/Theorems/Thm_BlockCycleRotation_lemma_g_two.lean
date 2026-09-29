-- Prove2me | Theorems.Thm_BlockCycleRotation_lemma_g_two
-- name    : BlockCycleRotation.lemma_g_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:26.950096+00:00
-- url     : https://prove2.me/theorems/300d896a-5da9-4e64-a8f2-ae9fd03f0370
-- title:
--   Lemma 16: $G_2(n) = O(n^{3/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$ there is $C_\varepsilon>0$ with
--   $$|G_2(n)| \le C_\varepsilon\, n^{3/2+\varepsilon} \qquad (n \ge 1).$$
--
--   $G_2$ collects the rounding discrepancies committed when each inner sum over an arithmetic progression is replaced by its expected length. Lemma 16 says these do not accumulate beyond the error already present, so they may be absorbed into the error term of Theorem 14.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 16. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L616-L620

import Definitions.Def_BlockCycleRotation_Theorem13
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.lemma_g_two {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → |G2sum n| ≤ C * (n : ℝ) ^ (3 / 2 + ε) := by sorry
