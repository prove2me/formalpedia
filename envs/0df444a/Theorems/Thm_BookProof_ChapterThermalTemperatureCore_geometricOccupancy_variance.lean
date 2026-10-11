-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_geometricOccupancy_variance
-- name    : BookProof.ChapterThermalTemperatureCore.geometricOccupancy_variance
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:24:33.519684+00:00
-- url     : https://prove2.me/theorems/53a4620a-db8b-4666-8bbf-9e75d98793a9
-- title:
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_variance` (h0 : 0 ≤ r) (h1 : r < 1) : (∑' n : ℕ, (n : ℝ) ^ 2 * geometricOccupancy r n) - (∑' n : ℕ, (n : ℝ) * geometricO
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_variance` (h0 : 0 ≤ r) (h1 : r < 1) : (∑' n : ℕ, (n : ℝ) ^ 2 * geometricOccupancy r n) - (∑' n : ℕ, (n : ℝ) * geometricOccupancy r n) ^ 2 = r / (1 - r) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.geometricOccupancy_variance`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_variance
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

theorem BookProof.ChapterThermalTemperatureCore.geometricOccupancy_variance (h0 : 0 ≤ r) (h1 : r < 1) :
    (∑' n : ℕ, (n : ℝ) ^ 2 * geometricOccupancy r n)
      - (∑' n : ℕ, (n : ℝ) * geometricOccupancy r n) ^ 2 = r / (1 - r) ^ 2 := by sorry
