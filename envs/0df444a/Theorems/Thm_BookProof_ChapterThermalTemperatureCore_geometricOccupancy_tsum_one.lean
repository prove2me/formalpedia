-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_geometricOccupancy_tsum_one
-- name    : BookProof.ChapterThermalTemperatureCore.geometricOccupancy_tsum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:24:23.705711+00:00
-- url     : https://prove2.me/theorems/0f67b101-7a15-4912-8de7-be0210f54c4b
-- title:
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_tsum_one` (h0 : 0 ≤ r) (h1 : r < 1) : ∑' n : ℕ, geometricOccupancy r n = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_tsum_one` (h0 : 0 ≤ r) (h1 : r < 1) : ∑' n : ℕ, geometricOccupancy r n = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_tsum_one`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_tsum_one
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

theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_tsum_one (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑' n : ℕ, geometricOccupancy r n = 1 := by sorry
