-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_dtBorn_temperature_coth
-- name    : BookProof.ChapterDisplacedThermalOverlap.dtBorn_temperature_coth
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:06:44.641983+00:00
-- url     : https://prove2.me/theorems/04d1bf33-0f11-4a7d-a84f-300869175d2a
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.dtBorn_temperature_coth` {x : ℝ} (hx : 0 < x) : ((BookProof.ChapterBoseEinstein.boseEinstein x).toNNReal : ℝ) + 1 / 2 = Real.cosh (x / 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.dtBorn_temperature_coth` {x : ℝ} (hx : 0 < x) : ((BookProof.ChapterBoseEinstein.boseEinstein x).toNNReal : ℝ) + 1 / 2 = Real.cosh (x / 2) / (2 * Real.sinh (x / 2))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.dtBorn_temperature_coth`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.dtBorn_temperature_coth
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterBoseEinstein
open BookProof.ChapterBoseEinstein
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.dtBorn_temperature_coth {x : ℝ} (hx : 0 < x) :
    ((BookProof.ChapterBoseEinstein.boseEinstein x).toNNReal : ℝ) + 1 / 2
      = Real.cosh (x / 2) / (2 * Real.sinh (x / 2)) := by sorry
