-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_displacedThermal_mean
-- name    : BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:02:09.688132+00:00
-- url     : https://prove2.me/theorems/cc1db5e7-9124-4957-8e97-6408686b94b2
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean` (a : ℝ) (nbar : ℝ≥0) : ∫ x, x ∂(displacedThermal a nbar) = a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean` (a : ℝ) (nbar : ℝ≥0) : ∫ x, x ∂(displacedThermal a nbar) = a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean (a : ℝ) (nbar : ℝ≥0) :
    ∫ x, x ∂(displacedThermal a nbar) = a := by sorry
