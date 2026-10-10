-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_dissipative_image_Icc
-- name    : BookProof.IrreversibleDynamics.dissipative_image_Icc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:20:24.622197+00:00
-- url     : https://prove2.me/theorems/7475c108-e475-4069-a334-66b7534ebd82
-- title:
--   `BookProof.IrreversibleDynamics.dissipative_image_Icc` (a b : ℝ) : dissipative '' Set.Icc a b = Set.Icc (a / 2) (b / 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.dissipative_image_Icc` (a b : ℝ) : dissipative '' Set.Icc a b = Set.Icc (a / 2) (b / 2)
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.dissipative_image_Icc`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.dissipative_image_Icc
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.dissipative_image_Icc (a b : ℝ) :
    dissipative '' Set.Icc a b = Set.Icc (a / 2) (b / 2) := by sorry
