-- Prove2me | Theorems.Thm_BlockCycleRotation_fBar_hasBoxIntegral
-- name    : BlockCycleRotation.fBar_hasBoxIntegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:29.00999+00:00
-- url     : https://prove2.me/theorems/2bccac3c-6f0e-4343-be85-ded72706722a
-- title:
--   Theorem 7: $f$ is Riemann integrable on $[0,1]$
-- statement:
--   The extension $\bar f$ of $f$ to the unit box is Riemann integrable, with Riemann integral equal to its Lebesgue integral:
--   $$\int_{[0,1]}^{\mathrm{Riemann}} \bar f = \int_{[0,1]} \bar f \, d\lambda .$$
--
--   This is the second half of Theorem 7, and the reason Theorem 9 can be proved by evaluating equally spaced Riemann sums: a bounded function continuous almost everywhere is Riemann integrable, and its Riemann integral agrees with the Lebesgue integral that the analysis actually computes.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 7. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L784-L793

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

set_option maxHeartbeats 1000000 in
-- The Riemann-Lebesgue criterion carries a large elaboration burden.

theorem BlockCycleRotation.fBar_hasBoxIntegral :
    HasIntegral unitBox IntegrationParams.Riemann FBar
      (BoxAdditiveMap.toSMul (MeasureTheory.Measure.toBoxAdditive volume))
      (∫ v in (unitBox : Set (Fin 1 → ℝ)), FBar v) := by sorry
