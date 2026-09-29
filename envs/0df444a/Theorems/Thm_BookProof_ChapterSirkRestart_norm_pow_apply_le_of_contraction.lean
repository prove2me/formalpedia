-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRestart_norm_pow_apply_le_of_contraction
-- name    : BookProof.ChapterSirkRestart.norm_pow_apply_le_of_contraction
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:24:43.751418+00:00
-- url     : https://prove2.me/theorems/89e7870b-119f-4fb3-9752-ff6930326909
-- title:
--   (S : E →L[ℂ] E) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖) (n : ℕ) (v : E) : ‖(S ^ n) v‖ ≤ ‖v‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRestart.norm_pow_apply_le_of_contraction` (module `BookProof.ChapterSirkRestart`), source chapter `BookProof/ChapterChapterSirkRestart.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRestart.lean

-- Generated from ChapterSirkRestart.lean — theorem BookProof.ChapterSirkRestart.norm_pow_apply_le_of_contraction
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart







noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterSirkRestart.norm_pow_apply_le_of_contraction (S : E →L[ℂ] E) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (n : ℕ) (v : E) : ‖(S ^ n) v‖ ≤ ‖v‖ := by sorry
