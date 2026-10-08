-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeShiftExample_shiftOp_adjoint
-- name    : BookProof.ChapterGaugeShiftExample.shiftOp_adjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T11:16:51.61999+00:00
-- url     : https://prove2.me/theorems/0e7942ca-c6b9-43bd-9746-38a54a51e42f
-- title:
--   `BookProof.ChapterGaugeShiftExample.shiftOp_adjoint` (m : ℤ) : ContinuousLinearMap.adjoint (shiftOp m) = shiftOp (-m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeShiftExample`.
--
--   `BookProof.ChapterGaugeShiftExample.shiftOp_adjoint` (m : ℤ) : ContinuousLinearMap.adjoint (shiftOp m) = shiftOp (-m)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeShiftExample.shiftOp_adjoint`.

-- Generated from ChapterGaugeShiftExample.lean — theorem BookProof.ChapterGaugeShiftExample.shiftOp_adjoint
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterGaugeShiftExample


open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

theorem BookProof.ChapterGaugeShiftExample.shiftOp_adjoint (m : ℤ) :
    ContinuousLinearMap.adjoint (shiftOp m) = shiftOp (-m) := by sorry
