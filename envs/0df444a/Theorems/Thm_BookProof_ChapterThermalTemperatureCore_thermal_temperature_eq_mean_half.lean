-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_thermal_temperature_eq_mean_half
-- name    : BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:24:54.611982+00:00
-- url     : https://prove2.me/theorems/48d2b47e-9280-4f74-81fd-dc5d1f3a6cb2
-- title:
--   `BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half` {x : ℝ} (hx : 0 < x) : Real.cosh (x / 2) / (2 * Real.sinh (x / 2)) = (∑' n : ℕ, (n : ℝ) * thermalProb (bo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half` {x : ℝ} (hx : 0 < x) : Real.cosh (x / 2) / (2 * Real.sinh (x / 2)) = (∑' n : ℕ, (n : ℝ) * thermalProb (boseEinstein x) n) + 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half
import Definitions.Def_ChapterCoherentOccupation
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterBoseEinstein
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterThermalTemperatureCore


noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}

theorem BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half {x : ℝ} (hx : 0 < x) :
    Real.cosh (x / 2) / (2 * Real.sinh (x / 2))
      = (∑' n : ℕ, (n : ℝ) * thermalProb (boseEinstein x) n) + 1 / 2 := by sorry
