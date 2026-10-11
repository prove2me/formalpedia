-- Prove2me | Theorems.Thm_BookProof_SmOneParticle_unitary_row_sum_normSq
-- name    : BookProof.SmOneParticle.unitary_row_sum_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:14:49.905238+00:00
-- url     : https://prove2.me/theorems/87d7f2a6-8061-4fbd-b422-1d8b621418f4
-- title:
--   `BookProof.SmOneParticle.unitary_row_sum_normSq` (hV : IsMixing V) (i : Fin 3) : ∑ j : Fin 3, ‖V i j‖ ^ 2 = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOneParticle`.
--
--   `BookProof.SmOneParticle.unitary_row_sum_normSq` (hV : IsMixing V) (i : Fin 3) : ∑ j : Fin 3, ‖V i j‖ ^ 2 = 1
--
--   Formalization note: Lean 4 identifier `BookProof.SmOneParticle.unitary_row_sum_normSq`.

-- Generated from ChapterSmOneParticle.lean — theorem BookProof.SmOneParticle.unitary_row_sum_normSq
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

variable {V U : Matrix (Fin 3) (Fin 3) ℂ}

theorem BookProof.SmOneParticle.unitary_row_sum_normSq (hV : IsMixing V) (i : Fin 3) :
    ∑ j : Fin 3, ‖V i j‖ ^ 2 = 1 := by sorry
