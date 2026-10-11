-- Prove2me | Theorems.Thm_BookProof_ChapterThermalTemperatureCore_half_integer_floor_coherent
-- name    : BookProof.ChapterThermalTemperatureCore.half_integer_floor_coherent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:04.645189+00:00
-- url     : https://prove2.me/theorems/efaca72f-f703-42f4-bdeb-6709669356b9
-- title:
--   `BookProof.ChapterThermalTemperatureCore.half_integer_floor_coherent` {lam : ℝ} (h : 0 ≤ lam) : 1 / 2 ≤ ∑' n : ℕ, ((n : ℝ) + 1 / 2) * coherentOccupation lam n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalTemperatureCore`.
--
--   `BookProof.ChapterThermalTemperatureCore.half_integer_floor_coherent` {lam : ℝ} (h : 0 ≤ lam) : 1 / 2 ≤ ∑' n : ℕ, ((n : ℝ) + 1 / 2) * coherentOccupation lam n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalTemperatureCore.half_integer_floor_coherent`.

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.half_integer_floor_coherent
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterBoseEinstein
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation
open BookProof.ChapterThermalTemperatureCore


noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}

theorem BookProof.ChapterThermalTemperatureCore.half_integer_floor_coherent {lam : ℝ} (h : 0 ≤ lam) :
    1 / 2 ≤ ∑' n : ℕ, ((n : ℝ) + 1 / 2) * coherentOccupation lam n := by sorry
