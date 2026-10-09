-- Prove2me | Theorems.Thm_BookProof_SchrodingerCutoff_exists_deriv_chi_bound
-- name    : BookProof.SchrodingerCutoff.exists_deriv_chi_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:33:42.890006+00:00
-- url     : https://prove2.me/theorems/02f9dbab-9cc2-42f2-9262-1e27a74f07ac
-- title:
--   The Lean 4 theorem `exists_deriv_chi_bound` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `exists_deriv_chi_bound` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchrodingerCutoffEsa.lean

-- Generated from ChapterSchrodingerCutoffEsa.lean — theorem BookProof.SchrodingerCutoff.exists_deriv_chi_bound
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterParityChirality
open BookProof.ChapterParityChirality
open BookProof.SchrodingerCutoff



open MeasureTheory Filter Complex

theorem BookProof.SchrodingerCutoff.exists_deriv_chi_bound : ∃ C : ℝ, 0 < C ∧ ∀ y, |deriv chi y| ≤ C := by sorry
