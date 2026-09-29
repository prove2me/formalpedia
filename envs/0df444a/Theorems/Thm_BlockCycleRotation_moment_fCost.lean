-- Prove2me | Theorems.Thm_BlockCycleRotation_moment_fCost
-- name    : BlockCycleRotation.moment_fCost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:59.018901+00:00
-- url     : https://prove2.me/theorems/d400b20d-bf79-42ed-a873-38ccd974f7a0
-- title:
--   Moments of $f$ under the uniform distribution on $[0,\tfrac12]$
-- statement:
--   For every $j$, if $X$ is uniform on $[0,\tfrac12]$ then
--   $$\mathbb{E}\bigl[f(X)^j\bigr] = \frac{\int_0^{1/2} f(x)^j\,dx}{1/2}.$$
--
--   The corollary to Theorem 7: since every power $f^j$ is bounded and continuous almost everywhere, it is integrable against the uniform law, so the cost distribution has moments of all orders and they are given by the corresponding integrals.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Corollary 8. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L1158-L1163

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.moment_fCost (j : ℕ) :
    ∫ x, fCost x ^ j ∂unifHalf = (∫ x in (0 : ℝ)..(1 / 2), fCost x ^ j) / (1 / 2) := by sorry
