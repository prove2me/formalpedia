-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_geometricOccupancy_nonneg
-- name    : BookProof.ChapterThermalTemperatureCore.geometricOccupancy_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:06:21.616983+00:00
-- url     : https://prove2.me/theorems/7ad7da16-5512-4779-bf29-86172b8dd67c
-- title:
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_nonneg` (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) : 0 ≤ geometricOccupancy r n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_nonneg` (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) : 0 ≤ geometricOccupancy r n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_nonneg`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_nonneg
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
open BookProof.ChapterThermalTemperatureCore


noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}

theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_nonneg (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    0 ≤ geometricOccupancy r n := by sorry
