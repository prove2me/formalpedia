-- Prove2me | Theorems.Thm_BlockCycleRotation_small_two_mul_gt
-- name    : BlockCycleRotation.small_two_mul_gt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:14:00.164827+00:00
-- url     : https://prove2.me/theorems/a25250b6-314c-4ffc-b94a-b8f82de2377a
-- title:
--   On the small branch, `2·d·a² > m`
-- statement:
--   **On the small branch, `2·d·a² > m`.** This is the paper's observation that `2a²` is bounded below by `m/d`, which is what makes the small part small.
--
--   In Blomer–Bux this is **Lemma 19**, “Small branch: `2d·a² > m`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1221-L1226

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.small_two_mul_gt {m d a a' b' : ℕ} (h : (a, a', b') ∈ gtTriples m d)
    (hsmall : m < d * a * (a + a')) : m < 2 * (d * a * a) := by sorry
