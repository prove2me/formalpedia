-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_thermal_temperature_eq_energy_expectation_coth
-- name    : BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_energy_expectation_coth
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:32.643989+00:00
-- url     : https://prove2.me/theorems/40a7b0d3-b835-418e-af4e-0c04cd3f61cc
-- title:
--   `BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_energy_expectation_coth` {x : ℝ} (hx : 0 < x) : Real.cosh (x / 2) / (2 * Real.sinh (x / 2)) = ∑' n : ℕ, ((n : ℝ) + 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_energy_expectation_coth` {x : ℝ} (hx : 0 < x) : Real.cosh (x / 2) / (2 * Real.sinh (x / 2)) = ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb (boseEinstein x) n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_energy_expectation_coth`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_energy_expectation_coth
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

theorem BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_energy_expectation_coth {x : ℝ} (hx : 0 < x) :
    Real.cosh (x / 2) / (2 * Real.sinh (x / 2))
      = ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb (boseEinstein x) n := by sorry
