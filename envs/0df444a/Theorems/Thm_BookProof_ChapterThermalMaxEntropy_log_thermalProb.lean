-- Prove2me | Theorems.Thm_BookProof_ChapterThermalMaxEntropy_log_thermalProb
-- name    : BookProof.ChapterThermalMaxEntropy.log_thermalProb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:43.127675+00:00
-- url     : https://prove2.me/theorems/854d51f0-9802-46d2-a36e-93c48e9e2b58
-- title:
--   `BookProof.ChapterThermalMaxEntropy.log_thermalProb` (h : 0 < nbar) (n : ℕ) : Real.log (thermalProb nbar n) = -Real.log (nbar + 1) + (n : ℝ) * Real.log (thermalRatio nbar)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalMaxEntropy`.
--
--   `BookProof.ChapterThermalMaxEntropy.log_thermalProb` (h : 0 < nbar) (n : ℕ) : Real.log (thermalProb nbar n) = -Real.log (nbar + 1) + (n : ℝ) * Real.log (thermalRatio nbar)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalMaxEntropy.log_thermalProb`.

-- Generated from ChapterThermalMaxEntropy.lean — theorem BookProof.ChapterThermalMaxEntropy.log_thermalProb
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

theorem BookProof.ChapterThermalMaxEntropy.log_thermalProb (h : 0 < nbar) (n : ℕ) :
    Real.log (thermalProb nbar n)
      = -Real.log (nbar + 1) + (n : ℝ) * Real.log (thermalRatio nbar) := by sorry
