-- Prove2me | Theorems.Thm_BookProof_ChapterPauliSU2_spinorAction_isHermitian
-- name    : BookProof.ChapterPauliSU2.spinorAction_isHermitian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:33:48.325366+00:00
-- url     : https://prove2.me/theorems/f37ae271-e83e-4ed7-a783-65b2d887e2e9
-- title:
--   `BookProof.ChapterPauliSU2.spinorAction_isHermitian` (T : Matrix (Fin 2) (Fin 2) ℂ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) : (spinorAction T X)ᴴ = spinorAction T X
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliSU2`.
--
--   `BookProof.ChapterPauliSU2.spinorAction_isHermitian` (T : Matrix (Fin 2) (Fin 2) ℂ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) : (spinorAction T X)ᴴ = spinorAction T X
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliSU2.spinorAction_isHermitian`.

-- Generated from ChapterPauliSU2.lean — theorem BookProof.ChapterPauliSU2.spinorAction_isHermitian
import Definitions.Def_ChapterPauliLorentz
import Mathlib
import Definitions.Def_ChapterPauliSU2
open BookProof.ChapterPauliSU2


open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

theorem BookProof.ChapterPauliSU2.spinorAction_isHermitian (T : Matrix (Fin 2) (Fin 2) ℂ)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) :
    (spinorAction T X)ᴴ = spinorAction T X := by sorry
