-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_thermal_plus_zeroPoint_conv
-- name    : BookProof.ChapterDisplacedThermalOverlap.thermal_plus_zeroPoint_conv
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:02:06.583583+00:00
-- url     : https://prove2.me/theorems/3fc88e43-0c29-4055-b1dc-b3b63d41c4ab
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.thermal_plus_zeroPoint_conv` (nbar : ℝ≥0) : (gaussianReal 0 nbar) ∗ (gaussianReal 0 (1 / 2)) = gaussianReal 0 (tauNN nbar)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.thermal_plus_zeroPoint_conv` (nbar : ℝ≥0) : (gaussianReal 0 nbar) ∗ (gaussianReal 0 (1 / 2)) = gaussianReal 0 (tauNN nbar)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.thermal_plus_zeroPoint_conv`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.thermal_plus_zeroPoint_conv
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.thermal_plus_zeroPoint_conv (nbar : ℝ≥0) :
    (gaussianReal 0 nbar) ∗ (gaussianReal 0 (1 / 2)) = gaussianReal 0 (tauNN nbar) := by sorry
