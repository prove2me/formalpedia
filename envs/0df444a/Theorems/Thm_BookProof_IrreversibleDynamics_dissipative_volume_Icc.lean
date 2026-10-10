-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_dissipative_volume_Icc
-- name    : BookProof.IrreversibleDynamics.dissipative_volume_Icc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:20:49.730991+00:00
-- url     : https://prove2.me/theorems/99ecca74-2d45-4437-b096-84c0cec05759
-- title:
--   `BookProof.IrreversibleDynamics.dissipative_volume_Icc` (a b : ℝ) : volume (dissipative '' Set.Icc a b) = ENNReal.ofReal ((b - a) / 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.dissipative_volume_Icc` (a b : ℝ) : volume (dissipative '' Set.Icc a b) = ENNReal.ofReal ((b - a) / 2)
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.dissipative_volume_Icc`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.dissipative_volume_Icc
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.dissipative_volume_Icc (a b : ℝ) :
    volume (dissipative '' Set.Icc a b) = ENNReal.ofReal ((b - a) / 2) := by sorry
