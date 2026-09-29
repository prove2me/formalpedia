-- Prove2me | Theorems.Thm_BlockCycleRotation_gtTriples_sq_lt
-- name    : BlockCycleRotation.gtTriples_sq_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:37.03299+00:00
-- url     : https://prove2.me/theorems/cb36d64f-390c-4164-9e2d-69ada61021f7
-- title:
--   The key restriction
-- statement:
--   **The key restriction.** On `gtTriples m d` we have `d·a² < m`, so `a ≤ √(m/d)`. This is what makes the error sum converge.
--
--   In Blomer–Bux this is **§4**, “Key restriction `d·a² < m`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L760-L765

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.gtTriples_sq_lt {m d a a' b' : ℕ} (h : (a, a', b') ∈ gtTriples m d) :
    d * a * a < m := by sorry
