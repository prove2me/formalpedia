-- Prove2me | Theorems.Thm_BookProof_ChapterBoseEinstein_thermalTemperature_boseEinstein_eq_coth
-- name    : BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:07:28.084988+00:00
-- url     : https://prove2.me/theorems/a05fb40c-b1e7-4b55-8834-f54aaa3b2cd3
-- title:
--   `BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth` (hx : 0 < x) : thermalTemperature (boseEinstein x) = Real.cosh (x / 2) / (2 * Real.sinh (x / 2))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBoseEinstein`.
--
--   `BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth` (hx : 0 < x) : thermalTemperature (boseEinstein x) = Real.cosh (x / 2) / (2 * Real.sinh (x / 2))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth`.

-- Generated from ChapterBoseEinstein.lean — theorem BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth
import Definitions.Def_ChapterCoherentOccupation
import Mathlib
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterBoseEinstein


noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

theorem BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth (hx : 0 < x) :
    thermalTemperature (boseEinstein x) = Real.cosh (x / 2) / (2 * Real.sinh (x / 2)) := by sorry
