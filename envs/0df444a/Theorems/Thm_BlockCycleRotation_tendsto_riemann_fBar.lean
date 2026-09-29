-- Prove2me | Theorems.Thm_BlockCycleRotation_tendsto_riemann_fBar
-- name    : BlockCycleRotation.tendsto_riemann_fBar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:28.727014+00:00
-- url     : https://prove2.me/theorems/fc68e12e-a006-4e72-ab10-35785907e252
-- title:
--   The evenly spaced Riemann sums converge
-- statement:
--   **The evenly spaced Riemann sums converge**, by instantiating Riemann integrability at the uniform subdivision.
--
--   In Blomer–Bux this is **Thm 9**, “Evenly spaced Riemann sums”. It is used in the proof of `theorem10_unit`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm 9. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L903-L925

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.tendsto_riemann_fBar :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ))) / (n : ℝ))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, fBar x)) := by sorry
