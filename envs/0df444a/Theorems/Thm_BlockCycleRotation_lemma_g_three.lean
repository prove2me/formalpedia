-- Prove2me | Theorems.Thm_BlockCycleRotation_lemma_g_three
-- name    : BlockCycleRotation.lemma_g_three
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:27.431065+00:00
-- url     : https://prove2.me/theorems/be3dc51d-073f-4f8b-acb0-1fbd8c279b90
-- title:
--   Lemma 18: $G_3(n) = O(n^{3/2+\varepsilon})$
-- statement:
--   For every $\varepsilon>0$ there is $C_\varepsilon>0$ with
--   $$|G_3(n)| \le C_\varepsilon\, n^{3/2+\varepsilon} \qquad (n \ge 1).$$
--
--   $G_3$ is the genuinely oscillating part: the deviation of the count of $b'$ in an arithmetic progression from its expected value, which is where the character sum estimates of §4 are used. The logarithmic loss from the divisor sum $\sum_{m \ne 0} 1/\min(m,a-m)$ is what the $n^{\varepsilon}$ absorbs.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L622-L626

import Definitions.Def_BlockCycleRotation_Theorem13
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.lemma_g_three {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → |G3sum n| ≤ C * (n : ℝ) ^ (3 / 2 + ε) := by sorry
