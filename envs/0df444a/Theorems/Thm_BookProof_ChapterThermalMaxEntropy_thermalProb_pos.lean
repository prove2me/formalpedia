-- Prove2me | Theorems.Thm_BookProof_ChapterThermalMaxEntropy_thermalProb_pos
-- name    : BookProof.ChapterThermalMaxEntropy.thermalProb_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:06:06.699727+00:00
-- url     : https://prove2.me/theorems/13e8c76a-1b10-46d5-a7bb-58ace3d76556
-- title:
--   `BookProof.ChapterThermalMaxEntropy.thermalProb_pos` (h : 0 < nbar) (n : ℕ) : 0 < thermalProb nbar n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalMaxEntropy`.
--
--   `BookProof.ChapterThermalMaxEntropy.thermalProb_pos` (h : 0 < nbar) (n : ℕ) : 0 < thermalProb nbar n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalMaxEntropy.thermalProb_pos`.

-- Generated from ChapterThermalMaxEntropy.lean — theorem BookProof.ChapterThermalMaxEntropy.thermalProb_pos
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

theorem BookProof.ChapterThermalMaxEntropy.thermalProb_pos (h : 0 < nbar) (n : ℕ) : 0 < thermalProb nbar n := by sorry
