-- Prove2me | Theorems.Thm_BlockCycleRotation_continuousAt_fCost
-- name    : BlockCycleRotation.continuousAt_fCost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:16.892451+00:00
-- url     : https://prove2.me/theorems/e8fd06ff-544f-49e3-9526-b953382137a4
-- title:
--   Theorem 7: $f$ is continuous at every irrational point of $(0,1)$
-- statement:
--   For irrational $x$ with $0 < x < 1$, the normalised cost function $f = 1+\psi$ is continuous at $x$.
--
--   The form of Theorem 7 used in the Riemann-sum argument: $f$ is the function whose values at rationals $k/n$ give the algorithm's average cost, and it is continuous off a set of measure zero.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 7. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L623-L651

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.continuousAt_fCost {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx : x < 1) :
    ContinuousAt fCost x := by sorry
