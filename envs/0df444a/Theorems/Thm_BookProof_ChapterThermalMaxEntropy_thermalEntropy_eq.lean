-- Prove2me | Theorems.Thm_BookProof_ChapterThermalMaxEntropy_thermalEntropy_eq
-- name    : BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:06:02.246459+00:00
-- url     : https://prove2.me/theorems/107e0ec6-0dc6-4120-b649-37cf8fb362ba
-- title:
--   `BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq` (h : 0 < nbar) : thermalEntropy nbar = Real.log (nbar + 1) - nbar * Real.log (thermalRatio nbar)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalMaxEntropy`.
--
--   `BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq` (h : 0 < nbar) : thermalEntropy nbar = Real.log (nbar + 1) - nbar * Real.log (thermalRatio nbar)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq`.

-- Generated from ChapterThermalMaxEntropy.lean — theorem BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Mathlib
import Definitions.Def_ChapterThermalMaxEntropy
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterThermalMaxEntropy


noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {nbar : ℝ}

theorem BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq (h : 0 < nbar) :
    thermalEntropy nbar = Real.log (nbar + 1) - nbar * Real.log (thermalRatio nbar) := by sorry
