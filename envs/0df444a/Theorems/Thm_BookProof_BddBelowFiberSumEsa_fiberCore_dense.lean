-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberCore_dense
-- name    : BookProof.BddBelowFiberSumEsa.fiberCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:09.605075+00:00
-- url     : https://prove2.me/theorems/20aa106c-43c5-443b-b613-63f2a3980f50
-- title:
--   The Lean 4 theorem `fiberCore_dense` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fiberCore_dense` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.fiberCore_dense
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.fiberCore_dense :
    Dense ((fiberCore ι : Submodule ℂ (fiberSpace ι)) : Set (fiberSpace ι)) := by sorry
