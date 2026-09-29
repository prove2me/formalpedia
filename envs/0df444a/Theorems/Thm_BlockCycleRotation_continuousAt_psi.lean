-- Prove2me | Theorems.Thm_BlockCycleRotation_continuousAt_psi
-- name    : BlockCycleRotation.continuousAt_psi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:07.576307+00:00
-- url     : https://prove2.me/theorems/c86188ed-36a3-4e06-9dd3-5961a5800dcd
-- title:
--   Theorem 7: $\psi$ is continuous at every irrational point
-- statement:
--   For irrational $x$ with $0 < x < \tfrac12$, the function $\psi$ is continuous at $x$.
--
--   This is the first half of Theorem 7. $\psi$ is defined by a self-similar recursion driven by the continued fraction expansion of its argument, and is discontinuous at every rational point; continuity at the irrationals is what makes the Riemann-integrability statement possible. The proof uses that the segments halve every two steps, so the recursion depth needed for a given accuracy is uniformly bounded near an irrational point.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 7. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L588-L621

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.continuousAt_psi {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx : x < 1 / 2) :
    ContinuousAt psi x := by sorry
