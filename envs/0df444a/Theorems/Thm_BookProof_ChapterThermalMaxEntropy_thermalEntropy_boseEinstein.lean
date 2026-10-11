-- Prove2me | Theorems.Thm_BookProof_ChapterThermalMaxEntropy_thermalEntropy_boseEinstein
-- name    : BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:06:24.156907+00:00
-- url     : https://prove2.me/theorems/f0a06e76-8bbe-48c0-b75b-e15604e22f24
-- title:
--   `BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein` {x : ℝ} (hx : 0 < x) : thermalEntropy (boseEinstein x) = -Real.log (1 - Real.exp (-x)) + x * boseEinstein x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalMaxEntropy`.
--
--   `BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein` {x : ℝ} (hx : 0 < x) : thermalEntropy (boseEinstein x) = -Real.log (1 - Real.exp (-x)) + x * boseEinstein x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein`.

-- Generated from ChapterThermalMaxEntropy.lean — theorem BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein
import Definitions.Def_ChapterCoherentOccupation
import Mathlib
import Definitions.Def_ChapterThermalMaxEntropy
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterBoseEinstein
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterThermalMaxEntropy


noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {nbar : ℝ}

theorem BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein {x : ℝ} (hx : 0 < x) :
    thermalEntropy (boseEinstein x)
      = -Real.log (1 - Real.exp (-x)) + x * boseEinstein x := by sorry
