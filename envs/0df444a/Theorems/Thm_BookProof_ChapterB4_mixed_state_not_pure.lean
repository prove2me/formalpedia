-- Prove2me | Theorems.Thm_BookProof_ChapterB4_mixed_state_not_pure
-- name    : BookProof.ChapterB4.mixed_state_not_pure
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:52:22.960245+00:00
-- url     : https://prove2.me/theorems/a34e668f-79e0-4879-8148-acc065231a18
-- title:
--   `BookProof.ChapterB4.mixed_state_not_pure` : ¬ IsPureState ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterB4`.
--
--   `BookProof.ChapterB4.mixed_state_not_pure` : ¬ IsPureState ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterB4.mixed_state_not_pure`.

-- Generated from ChapterB4.lean — theorem BookProof.ChapterB4.mixed_state_not_pure
import Mathlib
import Definitions.Def_ChapterB4
open BookProof.ChapterB4



open Matrix

noncomputable section

theorem BookProof.ChapterB4.mixed_state_not_pure :
    ¬ IsPureState ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by sorry
