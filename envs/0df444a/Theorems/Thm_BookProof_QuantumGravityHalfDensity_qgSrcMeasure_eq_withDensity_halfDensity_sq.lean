-- Prove2me | Theorems.Thm_BookProof_QuantumGravityHalfDensity_qgSrcMeasure_eq_withDensity_halfDensity_sq
-- name    : BookProof.QuantumGravityHalfDensity.qgSrcMeasure_eq_withDensity_halfDensity_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:39:19.454665+00:00
-- url     : https://prove2.me/theorems/29eb07ca-9478-46b5-bdd2-b58a987f1f05
-- title:
--   `BookProof.QuantumGravityHalfDensity.qgSrcMeasure_eq_withDensity_halfDensity_sq` : qgSrcMeasure = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun y => ENNReal.ofReal (qgHalfDen
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityHalfDensity`.
--
--   `BookProof.QuantumGravityHalfDensity.qgSrcMeasure_eq_withDensity_halfDensity_sq` : qgSrcMeasure = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun y => ENNReal.ofReal (qgHalfDensity y ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityHalfDensity.qgSrcMeasure_eq_withDensity_halfDensity_sq`.

-- Generated from ChapterQuantumGravityHalfDensity.lean — theorem BookProof.QuantumGravityHalfDensity.qgSrcMeasure_eq_withDensity_halfDensity_sq
import Mathlib
import Definitions.Def_ChapterQuantumGravityHalfDensity
open BookProof.QuantumGravityHalfDensity



open MeasureTheory Set Filter
open scoped ENNReal

theorem BookProof.QuantumGravityHalfDensity.qgSrcMeasure_eq_withDensity_halfDensity_sq :
    qgSrcMeasure
      = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          fun y => ENNReal.ofReal (qgHalfDensity y ^ 2) := by sorry
