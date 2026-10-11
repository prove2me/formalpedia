-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_geometricOccupancy_eq_thermalProb
-- name    : BookProof.ChapterThermalTemperatureCore.geometricOccupancy_eq_thermalProb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:06:32.304076+00:00
-- url     : https://prove2.me/theorems/9b367f05-6292-4a54-96a9-6578f748fb82
-- title:
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_eq_thermalProb` (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) : geometricOccupancy r n = thermalProb (geometricMean r) n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_eq_thermalProb` (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) : geometricOccupancy r n = thermalProb (geometricMean r) n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_eq_thermalProb`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_eq_thermalProb
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterThermalTemperatureCore


noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}

theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_eq_thermalProb (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    geometricOccupancy r n = thermalProb (geometricMean r) n := by sorry
