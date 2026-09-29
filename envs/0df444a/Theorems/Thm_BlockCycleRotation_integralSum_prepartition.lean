-- Prove2me | Theorems.Thm_BlockCycleRotation_integralSum_prepartition
-- name    : BlockCycleRotation.integralSum_prepartition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:36.266442+00:00
-- url     : https://prove2.me/theorems/1c64655b-10da-4625-bd92-7192f3137f27
-- title:
--   The integral sum of the uniform subdivision is the evenly spaced Riemann sum
-- statement:
--   The integral sum of the uniform subdivision is the evenly spaced Riemann sum.
--
--   In Blomer–Bux this is **Thm 9**, “Evenly spaced Riemann sums”. It is used in the proof of `tendsto_riemann_fBar`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 9. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L836-L871

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.integralSum_prepartition (n : ℕ) [NeZero n] :
    integralSum FBar (BoxAdditiveMap.toSMul (MeasureTheory.Measure.toBoxAdditive volume))
        (unitPartition.prepartition n unitBox)
      = (∑ j ∈ Finset.range n, fBar (((j : ℝ) + 1) / (n : ℝ))) / (n : ℝ) := by sorry
