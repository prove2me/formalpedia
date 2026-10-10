-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_dissipative_volume_image
-- name    : BookProof.IrreversibleDynamics.dissipative_volume_image
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:21:37.366305+00:00
-- url     : https://prove2.me/theorems/bd7da038-6830-4e66-ba52-a995ca8ef520
-- title:
--   `BookProof.IrreversibleDynamics.dissipative_volume_image` (A : Set ℝ) : volume (dissipative '' A) = volume A / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.dissipative_volume_image` (A : Set ℝ) : volume (dissipative '' A) = volume A / 2
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.dissipative_volume_image`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.dissipative_volume_image
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.dissipative_volume_image (A : Set ℝ) :
    volume (dissipative '' A) = volume A / 2 := by sorry
