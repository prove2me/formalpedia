-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaFourier_boostBlock_unitary
-- name    : BookProof.ChapterMajoranaFourier.boostBlock_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:56:38.82068+00:00
-- url     : https://prove2.me/theorems/464f45ef-c6f2-449d-ac49-a39458d75aef
-- title:
--   `BookProof.ChapterMajoranaFourier.boostBlock_unitary` {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : Aᴴ = A) (hA2 : A * A = 1) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : (boostBlock c s A)ᴴ * boo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaFourier`.
--
--   `BookProof.ChapterMajoranaFourier.boostBlock_unitary` {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : Aᴴ = A) (hA2 : A * A = 1) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : (boostBlock c s A)ᴴ * boostBlock c s A = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaFourier.boostBlock_unitary`.

-- Generated from ChapterMajoranaFourier.lean — theorem BookProof.ChapterMajoranaFourier.boostBlock_unitary
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
open BookProof.ChapterMajoranaFourier


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaFourier.boostBlock_unitary {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : Aᴴ = A)
    (hA2 : A * A = 1) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (boostBlock c s A)ᴴ * boostBlock c s A = 1 := by sorry
