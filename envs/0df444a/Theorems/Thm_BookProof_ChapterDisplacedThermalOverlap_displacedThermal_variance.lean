-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_displacedThermal_variance
-- name    : BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:02:44.941266+00:00
-- url     : https://prove2.me/theorems/bc6a796b-89f6-40e5-afc4-742e3f53ffe4
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance` (a : ℝ) (nbar : ℝ≥0) : Var[id; displacedThermal a nbar] = (nbar : ℝ) + 1 / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance` (a : ℝ) (nbar : ℝ≥0) : Var[id; displacedThermal a nbar] = (nbar : ℝ) + 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance (a : ℝ) (nbar : ℝ≥0) :
    Var[id; displacedThermal a nbar] = (nbar : ℝ) + 1 / 2 := by sorry
