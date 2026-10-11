-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_geometricMean_nonneg
-- name    : BookProof.ChapterThermalTemperatureCore.geometricMean_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:06:32.097975+00:00
-- url     : https://prove2.me/theorems/b5bfc8eb-1ffb-4bb5-808f-64be2e2c5392
-- title:
--   `BookProof.ChapterThermalTemperatureCore.geometricMean_nonneg` (h0 : 0 ≤ r) (h1 : r < 1) : 0 ≤ geometricMean r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.geometricMean_nonneg` (h0 : 0 ≤ r) (h1 : r < 1) : 0 ≤ geometricMean r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.geometricMean_nonneg`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.geometricMean_nonneg
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

theorem BookProof.ChapterThermalTemperatureCore.geometricMean_nonneg (h0 : 0 ≤ r) (h1 : r < 1) : 0 ≤ geometricMean r := by sorry
