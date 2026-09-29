-- Prove2me | Theorems.Thm_BlockCycleRotation_fBar_pow_hasBoxIntegral
-- name    : BlockCycleRotation.fBar_pow_hasBoxIntegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:49.132506+00:00
-- url     : https://prove2.me/theorems/a7b8d076-e590-4228-ac8c-fbbb313bfe85
-- title:
--   `f^j` is Riemann integrable
-- statement:
--   **`f^j` is Riemann integrable**, so the `j`-th moment exists.
--
--   In Blomer–Bux this is **Corollary 8**, “`f^j` Riemann integrable”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Corollary 8. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L1107-L1115

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

set_option maxHeartbeats 1000000 in
-- The Riemann-Lebesgue criterion carries a large elaboration burden.

theorem BlockCycleRotation.fBar_pow_hasBoxIntegral (j : ℕ) :
    HasIntegral unitBox IntegrationParams.Riemann (fun v : Fin 1 → ℝ => FBar v ^ j)
      (BoxAdditiveMap.toSMul (MeasureTheory.Measure.toBoxAdditive volume))
      (∫ v in (unitBox : Set (Fin 1 → ℝ)), FBar v ^ j) := by sorry
