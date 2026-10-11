-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_exists_boost_null
-- name    : BookProof.ChapterWignerLittleGroup.exists_boost_null
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:53:46.659972+00:00
-- url     : https://prove2.me/theorems/3efc1ae5-96a8-4e93-a0f5-4f5535b8a2c4
-- title:
--   `BookProof.ChapterWignerLittleGroup.exists_boost_null` (p : Fin 4 → ℝ) (hp0 : 0 < p 0) (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = 0) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.exists_boost_null` (p : Fin 4 → ℝ) (hp0 : 0 < p 0) (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = 0) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom nullMom) = hermOfMom p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.exists_boost_null`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.exists_boost_null
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.exists_boost_null (p : Fin 4 → ℝ) (hp0 : 0 < p 0)
    (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom nullMom) = hermOfMom p := by sorry
