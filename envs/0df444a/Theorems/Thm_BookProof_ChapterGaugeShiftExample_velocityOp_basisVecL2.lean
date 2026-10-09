-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeShiftExample_velocityOp_basisVecL2
-- name    : BookProof.ChapterGaugeShiftExample.velocityOp_basisVecL2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T11:18:09.120852+00:00
-- url     : https://prove2.me/theorems/c618f4e1-a721-4972-a694-b5d73d6f3ae9
-- title:
--   `BookProof.ChapterGaugeShiftExample.velocityOp_basisVecL2` (v : LinfZ) (j : ℤ) : velocityOp v (basisVecL2 j) = ((v : ℤ → ℝ) j : ℂ) • basisVecL2 j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeShiftExample`.
--
--   `BookProof.ChapterGaugeShiftExample.velocityOp_basisVecL2` (v : LinfZ) (j : ℤ) : velocityOp v (basisVecL2 j) = ((v : ℤ → ℝ) j : ℂ) • basisVecL2 j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeShiftExample.velocityOp_basisVecL2`.

-- Generated from ChapterGaugeShiftExample.lean — theorem BookProof.ChapterGaugeShiftExample.velocityOp_basisVecL2
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterGaugeShiftExample


open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

theorem BookProof.ChapterGaugeShiftExample.velocityOp_basisVecL2 (v : LinfZ) (j : ℤ) :
    velocityOp v (basisVecL2 j) = ((v : ℤ → ℝ) j : ℂ) • basisVecL2 j := by sorry
