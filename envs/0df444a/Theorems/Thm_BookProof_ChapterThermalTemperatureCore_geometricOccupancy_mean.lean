-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_geometricOccupancy_mean
-- name    : BookProof.ChapterThermalTemperatureCore.geometricOccupancy_mean
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:24:23.78937+00:00
-- url     : https://prove2.me/theorems/294c2c2e-11af-4ec7-9bed-35e52eac4629
-- title:
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_mean` (h0 : 0 ≤ r) (h1 : r < 1) : ∑' n : ℕ, (n : ℝ) * geometricOccupancy r n = r / (1 - r)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_mean` (h0 : 0 ≤ r) (h1 : r < 1) : ∑' n : ℕ, (n : ℝ) * geometricOccupancy r n = r / (1 - r)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_mean`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_mean
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

theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_mean (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑' n : ℕ, (n : ℝ) * geometricOccupancy r n = r / (1 - r) := by sorry
