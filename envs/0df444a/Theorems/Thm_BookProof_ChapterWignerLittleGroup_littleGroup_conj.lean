-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_littleGroup_conj
-- name    : BookProof.ChapterWignerLittleGroup.littleGroup_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:53:44.39064+00:00
-- url     : https://prove2.me/theorems/a7c1b9a9-4ec2-443a-8882-b52a5062fc17
-- title:
--   `BookProof.ChapterWignerLittleGroup.littleGroup_conj` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ} (h : act A (hermOfMom p) = hermOfMom q) : littleGroup q = (f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.littleGroup_conj` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ} (h : act A (hermOfMom p) = hermOfMom q) : littleGroup q = (fun B => A * B * A⁻¹) '' littleGroup p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.littleGroup_conj`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.littleGroup_conj
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.littleGroup_conj {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ}
    (h : act A (hermOfMom p) = hermOfMom q) :
    littleGroup q = (fun B => A * B * A⁻¹) '' littleGroup p := by sorry
