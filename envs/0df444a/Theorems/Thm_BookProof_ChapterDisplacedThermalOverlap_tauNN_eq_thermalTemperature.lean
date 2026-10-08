-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_tauNN_eq_thermalTemperature
-- name    : BookProof.ChapterDisplacedThermalOverlap.tauNN_eq_thermalTemperature
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:01:52.145451+00:00
-- url     : https://prove2.me/theorems/bd4b70e2-1610-48d5-bee9-6e589b2d6480
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.tauNN_eq_thermalTemperature` (nbar : ℝ≥0) : ((tauNN nbar : ℝ≥0) : ℝ) = BookProof.ChapterCoherentTemperature.thermalTemperature (nbar : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.tauNN_eq_thermalTemperature` (nbar : ℝ≥0) : ((tauNN nbar : ℝ≥0) : ℝ) = BookProof.ChapterCoherentTemperature.thermalTemperature (nbar : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.tauNN_eq_thermalTemperature`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.tauNN_eq_thermalTemperature
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.tauNN_eq_thermalTemperature (nbar : ℝ≥0) :
    ((tauNN nbar : ℝ≥0) : ℝ)
      = BookProof.ChapterCoherentTemperature.thermalTemperature (nbar : ℝ) := by sorry
