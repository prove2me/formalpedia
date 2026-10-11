-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_half_integer_floor
-- name    : BookProof.ChapterThermalTemperatureCore.half_integer_floor
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:24:31.291988+00:00
-- url     : https://prove2.me/theorems/18dd76d3-8a05-488d-91b9-c8601219ecf8
-- title:
--   `BookProof.ChapterThermalTemperatureCore.half_integer_floor` {nbar : ℝ} (h : 0 ≤ nbar) : 1 / 2 ≤ (∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n) ∧ ((∑' n : ℕ, ((n : ℝ) + 1 / 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.half_integer_floor` {nbar : ℝ} (h : 0 ≤ nbar) : 1 / 2 ≤ (∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n) ∧ ((∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n) = 1 / 2 ↔ nbar = 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.half_integer_floor`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.half_integer_floor
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

theorem BookProof.ChapterThermalTemperatureCore.half_integer_floor {nbar : ℝ} (h : 0 ≤ nbar) :
    1 / 2 ≤ (∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n) ∧
      ((∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n) = 1 / 2 ↔ nbar = 0) := by sorry
