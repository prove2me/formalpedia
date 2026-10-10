-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_dtOverlap_lt_of_dist_lt
-- name    : BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:03:55.487898+00:00
-- url     : https://prove2.me/theorems/9bee33b7-b69f-410e-aebd-2e31b6fc2300
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt` (nbar : ℝ≥0) {a b c : ℝ} (h : (a - b) ^ 2 < (a - c) ^ 2) : dtOverlap nbar a c < dtOverlap nbar a b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt` (nbar : ℝ≥0) {a b c : ℝ} (h : (a - b) ^ 2 < (a - c) ^ 2) : dtOverlap nbar a c < dtOverlap nbar a b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt (nbar : ℝ≥0) {a b c : ℝ}
    (h : (a - b) ^ 2 < (a - c) ^ 2) : dtOverlap nbar a c < dtOverlap nbar a b := by sorry
