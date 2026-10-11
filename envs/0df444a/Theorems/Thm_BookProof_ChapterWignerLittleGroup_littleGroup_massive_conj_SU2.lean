-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_littleGroup_massive_conj_SU2
-- name    : BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:53:45.157128+00:00
-- url     : https://prove2.me/theorems/fd80fd82-e0f8-4aaa-b7fc-03345852a8ee
-- title:
--   `BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2` {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hp0 : 0 < p 0) (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = m ^ 2) : ∃
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2` {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hp0 : 0 < p 0) (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = m ^ 2) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ littleGroup p = (fun B => A * B * A⁻¹) '' SU2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2 {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hp0 : 0 < p 0)
    (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = m ^ 2) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      littleGroup p = (fun B => A * B * A⁻¹) '' SU2 := by sorry
