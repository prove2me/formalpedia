-- Prove2me | Theorems.Thm_BookProof_ChapterB4_mixed_state_satisfies_both
-- name    : BookProof.ChapterB4.mixed_state_satisfies_both
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:52:18.110718+00:00
-- url     : https://prove2.me/theorems/3ef09ca5-778c-4b56-b514-4a86c6dc1d73
-- title:
--   `BookProof.ChapterB4.mixed_state_satisfies_both` : Matrix.trace (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * P1) = 1 / 2 ∧ Matrix.trace (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterB4`.
--
--   `BookProof.ChapterB4.mixed_state_satisfies_both` : Matrix.trace (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * P1) = 1 / 2 ∧ Matrix.trace (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * P2) = 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterB4.mixed_state_satisfies_both`.

-- Generated from ChapterB4.lean — theorem BookProof.ChapterB4.mixed_state_satisfies_both
import Mathlib
import Definitions.Def_ChapterB4
open BookProof.ChapterB4



open Matrix

noncomputable section

theorem BookProof.ChapterB4.mixed_state_satisfies_both :
    Matrix.trace (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * P1) = 1 / 2 ∧
    Matrix.trace (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * P2) = 1 / 2 := by sorry
